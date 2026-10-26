# Limitations

The trusted computing base, and what is deliberately not proven yet. Kept honest
so that a claim does not read as stronger than its evidence, and corrected when it does.

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

The GF(2^16) field is no longer where this matters. Until 2026-10-01
`Model.Gf65536.mul_assoc`, the statement that this is a field and not merely
probably a field, rested on about forty such axioms, and
`Model.Gf65536.mul_inv_cancel`, that every nonzero element inverts, on
`native_decide`. Every law of the field, the inverse of every nonzero element,
`Model.Polynomial.interp_eq` and the translated field arithmetic
`Tacenta.ErasureT3.mul_refines` are now proved by the kernel: `#print axioms`
shows `propext`, `Classical.choice` and `Quot.sound` and nothing else. The
operations are linear over GF(2), so each law follows from the law on the sixteen
basis elements, which the kernel evaluates directly, and the inverses follow from
the order of two, a closed computation (the comment "What is established" in
`Model/Gf65536.lean`). Where `bv_decide` remains is the composite header's
big-endian round trips (`Model.CompositeHeader`, `Serialization.readBe32_be32`),
and the compiler-trust facts listed below.

**Where this is and is not the case is pinned by the build, not described.**
`Proofs.TrustedBase` prints the axioms of the load-bearing theorems under
`#guard_msgs`, so a proof that starts trusting something new fails there: the
Braid's epoch accounting, the classical ratchet's five T2 theorems, the field
and interpolation results, the composite header, and the model-level theorems
of `Properties/` and of `Proofs.KeyErasure`, `Proofs.MemorySafety` and
`Proofs.SparseRatchetCorrectness` that `CLAIMS.md` names (all but
`Properties.StateConsistency.ageStore_preserves_the_rest`, for which
`#print axioms` reported no axiom when this was written; it has no pin, so
nothing in the build holds that). `Translation.T1` and
`Translation.T3` do the same for the classical ratchet's T1 and T3 headline
theorems (`send_refines`, `receive_refines`, `message_keys_refines`),
`Translation.SessionT1`/`SessionT3` for the session's,
`Translation.ErasureT1`/`ErasureT3` for the erasure coder's two entry points
and its field, and `Translation.ProtobufT1`/`ProtobufT3` for both message
parsers, the encoder and all nine refinement theorems.
`Translation.UnitLifecyclePublicT1` pins the six Session lifecycle results, five
panic-freedom theorems and one lemma (`encrypt_no_panic`, `decrypt_no_panic`,
`decrypt_ratchet_no_panic`, `establish_initiator_for_no_panic`,
`establish_responder_no_panic` and `invariant_gives_preconditions`); none
depends on a compiler-trust axiom. Three of the five panic-freedom theorems
(`decrypt_no_panic`, `decrypt_ratchet_no_panic` and `establish_responder_no_panic`) took a
record with a false field until it was restated for bounded decoders. The four records follow from an
axiom base that one interpretation satisfies, under five laws about standard-library and `zeroize`
operations. That is an argument about derivations. The headroom records are shown satisfiable in the same
sense, with the inhabitedness of the opaque types (one of them, the key pair, an assumption) and two further assumptions in the
base, one about the DH primitives and one about `Option::eq`, which no proof here checks against the real functions (the
subsection "The four contract records follow from an axiom base that has a model, under five laws", paragraph "The headroom
records"; `GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`).
`Translation.ImportInv` pins both halves of its chain: the two ratchets'
`invariant_true_iff` and `from_bytes_establishes_inv`, together with the
classical ratchet's two non-vacuity pins, which are kernel-only; and
separately the Braid's `from_bytes_establishes_inv` and each of the four
`decoded_*` corollaries, which are not -- the Braid's reaches the opaque
erasure and KEM decoders and, through its `invariant`'s key-pair clause, the
KEM's `header`, `ek_vector` and `validate_ek`, and a corollary carries the
boundary axioms of the
`receive` theorem it composes with, the sparse ratchet's carrying no
compiler-trust axiom since 2026-09-30. `Translation.SpqrT1`/`SpqrT3` pin the sparse
ratchet's `send` and `receive`, for panic-freedom and for refinement, and
`Translation.BraidT1`/`BraidT3` the Braid's; the bases stated below for those
crates' other theorems are read off `#print axioms` by hand. Ten of the Triple
Ratchet's theorems on the three-leaf unit are pinned in
`Translation/UnitPins.lean` -- composed `send`, `receive` and `clone`, three
accessors, the two bundle proofs and the two discharged refinements -- beside
the unit's copies of the two inner ratchets' pinned theorems, and the rest of
its T1/T3 are read off by hand. Some results are on the
kernel alone and are worth knowing as such. The ML-KEM Braid's epoch accounting
depends on `propext` and `Quot.sound`, nothing more. That is the calculation on
which both sides must agree exactly, so having it on the kernel rather than on
a compiler is worth the line.

Most other uses of `native_decide` (about a hundred) are in `example`
declarations. Those are build-time known-answer checks: they fail the build if
wrong, and no theorem depends on them, so they widen no proof's trust base.

**None is inside a translation theorem since 2026-10-21.** Until then thirteen were: `fPrefix_agrees` and
`skInfo_agrees` in `Translation.SessionT3`; in `Translation.SpqrT3`, `protocol_info_agrees`,
`chain_start_agrees`, `root_label_agrees`, `chain_label_agrees`,
`max_skip_agrees`, `max_skipped_store_agrees`, `max_skip_val`, and one step of
`receive_refines_continuation` (that `(1 : U64)` has value 1); and in `Translation.UnitTripleT3`, `split_info_agrees`,
`combine_info_agrees`, and one step of `split_secret_refines`. The generated copies on the three-leaf unit
(`UnitSpqrT3.lean`) and on the eight-leaf Session unit (`SessionUnitSpqrT3.lean`,
`SessionUnitTripleT3.lean`) carried those again, and through the Session unit's copies nine of them, the four labels,
the two skip bounds and `MAX_SKIP`'s value, the `(1 : U64)` step and the combine label, reached every lifecycle
refinement that composes the sparse or the Triple receive, the encrypt route and the responder's receipt (78 pinned
results). Each was a closed numeric or byte-string fact. The translation marks the constants `@[global_simps,
irreducible]`, so `rfl` and `decide` do not unfold them and `native_decide` evaluated them instead; `simp` with the
constant's name unfolds them, and each is now proved by `simp` and `rfl`, by `simp`, or (the `(1 : U64)` step) by
`decide`, with the same statement; the zero-array step of `split_secret_refines`, which the proof never used, is
removed. Every pin that listed one of their axioms lost exactly that axiom, and the Session
unit's eleven are pinned in `Translation/AxiomAuditSessionUnit.lean` with the kernel's three axioms (the two that are
refinements, `receive_refines_continuation` and `split_secret_refines`, with the unit's opaque constants too).
Two earlier uses were removed on 2026-09-30, in `Translation.SpqrT1.receive_no_panic` (settled by `decide`) and in
`UnitLifecycleT1.full_store_eq_no_panic` (settled by `simp`), and a fourteenth, `Model.Gf65536.mul_inv_cancel`, has been
proved by the kernel since 2026-10-01. On Lean v4.31.0 the axiom each such use adds is the per-declaration
`<decl>._native.native_decide.ax_*` (and `…bv_decide.ax_*` for `bv_decide`), not `Lean.ofReduceBool`; either way it
puts the compiler into the axiom base of every theorem downstream. `attest.py`'s `COMPILER_TRUSTED_PINS` lists the
pinned results that may still carry one, exactly: it refuses a compiler-trusted pin not on it and an entry whose pin
lists none. Since 2026-10-21 it holds twelve: `Proofs.Serialization.decode_encode_composite` (three `bv_decide`
lemmas of the composite header) and the eleven statements that name `Session::export` or `Session::import` (the
`toStr` axiom, next paragraph but one). The headline theorems of the classical and sparse ratchets, the
Braid, the session, the erasure coder and the parser are pinned under
`#guard_msgs`, and ten of the Triple Ratchet's on the unit, so a new
`native_decide` reaching one of them fails the build.

Kernel-checked is not kernel-only. The lifecycle results the nine constants reached are now kernel-checked over the
unit's opaque constants: their pins list the kernel's three axioms and the declarations of what the translation could
not see (the primitives, `zeroize`, `Vec`, `Option` and the RNG). Those are data- and type-valued, so a theorem listing
them assumes no proposition about them beyond its hypotheses, and says nothing about the real primitives unless its
hypotheses hold of them.

**The generated translation carries compiler-trust axioms of its own**,
346 across the 11 generated modules at `dea57eaf` (the line printed by `attest.py --compare-audit`, which the `translation` job runs through `no-sorry.sh`; run 36629026947). Aeneas's `toStr` discharges its
string-length bound with `by decide +native`, so every generated `Debug`
`fmt` body (one per error and header type) adds axioms named
`<fmt>._native.decide.ax_*`, each stating `decide (s.toByteArray.size ≤
U32.max) = true` for a string literal. No pinned theorem depends on one of those -- a
`Debug` formatter is on no proof's path -- and `attest.py` would classify a
pin that did as compiler-trusted rather than kernel-only. They are not
opaque externals and are not in `manifests/translation-attestation.json`;
the axiom audit accepts them under the same shape rule as the hand-written
`native_decide` uses (name, statement, a parent in the same module, and
that parent's own value applying the axiom -- here through the `_proof_n`
auxiliary the elaborator splits out of a `fmt` body) and prints them apart
from the externals, as `audit-native:` lines in the translation build log,
so the count is visible rather than folded in.

One axiom of the same kind does reach pinned theorems. The size checks
`debug_assert_eq!(out.len(), capacity, "the size arithmetic above drifted from the encoding")` in `Session::export` and,
with the same text, in `PrekeyStore::to_bytes` give the Session unit two axioms with that proposition and the same type,
`tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1` and
`tacenta_session_unit.lifecycle.Session.export._native.decide.ax_1`; `#print axioms` of `Session.export` itself, and of
every pinned statement that names `export` or `import`, lists only the first (the export check reaches it through the
auxiliary proof the two definitions share). Those statements, eleven pinned results in all, are the compiler-trusted pins
of the lifecycle. The proposition is true and the kernel shows it: `UnitLifecycleSessionRoundTrip.export_message_fits`
states it (the same expression as the axiom's type, which `scripts/check-discharge-native-decide-negatives.py` checks)
and is proved with `propext` only (`String.size_toByteArray` and a `decide` on the literal's byte size; plain `decide`
does not reduce it). The dependency stays: the generated definition refers to the axiom, not to the theorem, and no proof
can redirect it. **Retained blocker:** removing it needs the message dropped from that `debug_assert_eq!` (a verified-zone
change; whether Charon then emits no string literal is not checked) or an Aeneas `toStr` whose default bound proof the
kernel can check, then a re-translation and a pin refresh.

Eleven of them (counted on an earlier generation and not recounted) meet every part of that rule except the last, and
the audit waives it for them. All eleven are in the three-leaf translation unit
described under "The three-leaf translation unit" below, which puts all three
leaves' types in one module. Eight string literals occur in more than one
leaf's `Debug` body, `decide +native` caches its result by statement, and the
second and third occurrence of a literal reuse the first's proof -- leaving the
axiom named after each later declaration declared and reached by nothing. The
waiver is exactly that: an axiom no first-party declaration mentions, in a
value or in a statement, need not be applied by its parent. Such an axiom is in
no theorem's `#print axioms` and so widens no trust base, and the moment
anything mentions it the requirement is back. It is not extended to
`_unsafe_rec`, which the code generator calls by name whether or not anything
mentions it. `check-audit-negatives.sh` plants each condition of the rule,
including this waiver's, and fails if the audit calls any of them wrongly.

That shape is one elaboration-time code could plant, and the audit could not
tell a planted one from these; "Trusted, not verified" below says what
excludes it.

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
  regenerating, and what any linux-x86_64 reader can check the same way
  (`scripts/regenerate-in-container.sh` does so in a container, and
  `REPRODUCING.md` records one run of it by the maintainer's tool-assisted
  session, which was not independent).
- A declaration added with `set_option debug.skipKernelTC true` is checked
  by the elaborator and not by the kernel, and nothing in the environment
  says so afterwards. `Model.AxiomAudit`, which every package's build runs,
  refuses axioms, opaques, unsafe and partial declarations and
  `implemented_by`/`extern` from the elaborated environment, but cannot see
  this one; `scripts/check-lean-constructs.sh` refuses the option textually,
  and `no-sorry.sh` replays every first-party module through the kernel with
  `leanchecker`, which is the check that actually settles it. `leanchecker`
  is Lean's own kernel rerun over the oleans, not an independent checker.
- The axiom audit's two allowances are recognised by shape, and the shape
  can be planted. `Model.AxiomAudit` accepts a `<t>._native.<tactic>.ax_*`
  axiom that states a compiled Boolean evaluation returned `true` and is
  applied by `<t>`'s own proof term, because that is what `native_decide`
  and `bv_decide` produce; and a partial, self-calling `<f>._unsafe_rec`
  beside a safe, recursive `<f>` of the same type, because that is what the
  compiler produces. Code that runs at elaboration time -- a `run_cmd`, a
  `#eval`, an `elab`, a `macro`, an `initialize` -- can call `addDecl` and
  produce exactly that: an axiom `<t>._native.native_decide.ax_1_1 : decide
  False = true` with its name assembled from string literals, and a theorem
  applying it, after which `(1 : Nat) = 2`; or `addAndCompile` a
  `<f>._unsafe_rec` with a different body beside a recursive `<f>`, after
  which `native_decide` proves things of `<f>` that are false of it.
  `leanchecker` accepts both, since an axiom is a kernel-valid declaration.
  **The audit cannot distinguish a planted compiler-trust axiom or
  auxiliary from a real one on shape alone.** What excludes them is the
  textual rule in `scripts/check-lean-constructs.sh` that hand-written
  first-party Lean contains no elaboration-time code at all -- no
  `run_cmd`, `#eval`, `elab`, `macro`, `syntax`, `initialize`, `addDecl`,
  and no reference to the `Lean` namespace, which is where every such API
  lives -- outside `Model/AxiomAudit.lean`'s own implementation and the
  seven `run_cmd _root_.Model.AxiomAudit.run` lines, allow-listed by file path and
  exact line content and each standing alone (at column 0, no wrapper
  before, nothing after but another invocation, in a module of imports, pins
  and the invocation), so that an invocation written any other way fails
  there and a second one in an audit module fails in the reach check below
  (the refuted-record walk of `CLAIMS.md`'s vacuity section runs as a
  compiled executable over each closure, not from a module). The scan's
  rules read text and are defence in depth around those seven lines, not a
  tokenizer: eighteen hostile reads each found a new spelling of Lean's
  surface syntax, and the last ones were closed by refusing whole classes
  (every `ident!` macro followed by a string or bracket and every message
  head outside the audit, any brace in a string literal inside it, any
  lakefile change) rather than spellings, by making the stripper read a
  top-level `/-…` and `λ` as Lean does, and by refusing any file in which
  the stripper's reading of a char literal or raw string depends on the
  character before it, or in which a literal or comment opener follows
  anything but whitespace, an opening bracket or a comma (Lean reads those
  only at a token boundary; the stripper reads them anywhere, and no honest
  first-party file has one after anything else), or which holds a carriage
  return or a NUL (Lean ends a line at a newline or at CRLF only; the
  scan's reading would end one at a lone carriage return too, so both
  stripper copies refuse such a file, CRLF included: the tree is LF-only);
  `scripts/check-audit-reach.sh`, which fails if any first-party module is
  outside the seven audit modules' import closure, so that no module holds
  such a declaration unwalked, and fails if the seven do not all run with the
  same first-party prefixes, and if any of them invokes the audit more than
  once or in a form the prefix check cannot read; and
  `scripts/check-audit-negatives.sh`, which plants one declaration for each
  kind the audit refuses and one for the shape it allows, and fails if the
  audit decides any of them wrongly. The grep is what it is: a construct the
  stripper mishandles, or a route to the environment that names none of
  those tokens, would be a hole in this rule and not something the audit
  would catch.
- The Mathlib build artifacts the T1/T3 build loads are trusted. `lake exe cache
  get` fetches prebuilt `.olean` files for the pinned Mathlib commit from
  Mathlib's cache over HTTPS with no signature, and Lean loads an olean without
  re-checking it against its source. The manifest pins which Mathlib commit is
  *meant*; the cache decides what is *loaded*. Building Mathlib from source
  removes this edge and costs hours, which is why it is a trust rather than a
  step.
- The cryptographic primitives are trusted, except the key derivation. tacenta-core uses
  vetted crates for X25519, AES-256-CBC, Ed25519, the SHA-256 and HMAC that the root crate's identity and group
  digests and the AEAD's tag check on decryption call, the SHA-512 inside XEdDSA, and ML-KEM-1024 from
  libcrux-ml-kem. Since the KDF change (ADR-0010)
  `tacenta-kdf`'s HMAC-SHA256 and HKDF-SHA256 are a SHA-256, an HMAC and an HKDF copied here (pinned in
  `kdf/src/lib.rs` by commit and file digests, and under this repository's licence, Apache-2.0), translated, and proved of the
  Session unit's translation to compute tacenta-model's `Model.Kdf.hmac` and `Model.Kdf.hkdf`
  (`UnitLifecycleKdf.hmacAgrees`, `hkdfAgrees`), and of the classical ratchet's, the PQXDH session's, the sparse
  ratchet's, the Braid's and the three-leaf unit's copies by the same proofs ported (`KdfLeafAgreements`,
  `KdfTripleUnitAgreements`). The lifecycle and Braid-and-erasure translations include the bodies too, with no
  theorem about them. What stays trusted about them: that tacenta-model's KDF is
  RFC 4231's and RFC 5869's (vectors, not proof), the translation's fidelity, their timing (an inventory of the
  compiled branches is read, not proved; "Constant-time behaviour" below), and their erasure (none: the copied
  code wipes no intermediate, as the RustCrypto crates with the features this crate enabled did not either).
  The copied code was written by the maintainer with tool assistance in a separate, unpublished repository; the three Rust files were read in full by the maintainer on 2026-10-23, and before that only by tool-assisted sessions; no reader independent of the maintainer has read the three files, and no human has read their proofs. Its cost, measured on one x86_64 Linux machine with SHA extensions (ADR-0010, Costs): per call 5.1 to 18.5 times slower than the shipping RustCrypto (which uses the SHA extensions there) and 1.37 to 2.16 times slower than RustCrypto built without them; at protocol level, on that machine only, one 16-byte encrypt and decrypt round 1.12 times, encrypt alone 2.9 to 3.8 times and decrypt after 500 lost messages 4.5 times. The source repository's own machine measured the per-call cost only. None of this covers the AEAD: `aead::encrypt` stays an opaque axiom of every
  translation, and no theorem says how it computes its tag. On encryption that tag now comes from the copied
  HMAC, while decryption checks it with RustCrypto's `hmac` and `sha2` (`boundary/src/aead.rs`); that the two
  compute the same tag rests on tests (`kdf/tests/differential.rs` and the AEAD round-trip tests), not on
  proof. The crate's top-level ML-KEM-1024 functions carry hax and F*
  annotations by its own account, and this project has not checked which are
  discharged. The three top-level functions this project calls are marked
  `verification_status(panic_free)` in the pinned source, and the verification
  status file the crate's README cites is not in the published package. The
  incremental interface that `tacenta-kem` uses for the Braid
  carries no such annotations in the pinned version 0.0.10. Both are trusted,
  not verified. Two primitives are implemented here rather than taken from a
  vetted crate: XEdDSA, over curve25519-dalek and ed25519-dalek, the exception
  recorded in ADR-0002, and since the KDF change the key derivation's SHA-256, HMAC
  and HKDF above, the exception ADR-0010 records. The model computes SHA-256, HMAC, and HKDF itself as the vector
  oracle and, in the six translations whose theorems take the key derivation's
  hypotheses, as the definitions the copied code is proved to compute; that
  those definitions are the RFCs' rests on the vectors, which anchor them to RFC
  and NIST values.
- Diffie-Hellman agreement and the AEAD are boundary primitives in the model: it
  consumes DH outputs as bytes and stops at the AEAD material. The model's
  vectors therefore assert the key schedule, not ciphertext bytes.
- **The boundary hypotheses about opaque operations are stated under the
  Rust operation's own precondition, where it has one.** An opaque operation
  the translation cannot see is described by a named hypothesis, and each of
  those that used to claim more than the Rust operation delivers now carries
  the condition under which the Rust returns, discharged in the proof at
  every use rather than argued from the call sites in prose. The HKDF
  hypotheses -- `HkdfTotal` and `HkdfAgrees` (`T1.lean`/`T3.lean`),
  `SessionT1.HkdfTotal`, the Braid's and the Triple's `HkdfSha256Total`,
  `BraidHkdfAgrees`, `SpqrHkdfAgrees` and `TripleHkdfAgrees` -- carry
  `N.val ≤ 8160`, RFC 5869's `255 · HashLen`, which is the bound the crate's
  `assert!` enforces (its `expect` until the KDF change (ADR-0010), with the same panic text); every call site asks for 32, 64, 80 or 96 bytes and the
  premise closes from the literal (`KdfCkTotal` and `KdfRkTotal` are about
  the sparse ratchet's own fixed-length wrappers, total in Rust, and were
  never in this list). The classical `T1.RemoveSkippedAtTotal` and
  sparse `RemoveSkippedAtTotal`/`RemoveSkippedAtAgrees` carry
  `i.val < v.val.length`; every call site sits under exactly that loop
  guard, from which the proof discharges the premise, and the guard also
  removed the `[Inhabited T]` bound the unguarded statements needed for
  consistency. They are statements about translated removal helpers and not about an
  opaque `Vec::remove`, which the translations no longer call, so the model and the refutation
  of the unguarded shape that `Translation/Satisfiability.lean` keeps are retired and bridged to
  nothing; the hypotheses are shown to follow from named laws in `SatisfiabilityRatchetLaws.lean`,
  `SatisfiabilitySpqrLaws.lean` and `UnitSatisfiabilityTripleLaws.lean`. `DivCeilTotal` carries `b.val ≠ 0`, its one divisor being the
  constant `CHUNK_BYTES`. `KeyPairGenerateTotal`, `Encapsulate1Total` and
  the two randomness-drawing clauses of `KemAgreesFor` carry
  `BraidT1.RngTotal rc`, that the caller's `fill_bytes` returns, which the
  real `generate`/`encapsulate1` need since they fill their randomness from
  it; `step_send_no_panic`, `send_no_panic`, `step_send_refines` and
  `Braid.send_refines` take it for the RNG they are handed. What remains
  stronger than the Rust is listed where it belongs: `BraidT1.lean`'s five totals over the erasure coder
  (`EncoderNewTotal`, `EncoderNextChunkTotal`, `DecoderNewTotal`,
  `DecoderAddChunkTotal`, `DecoderMessageTotal`), which are the same
  shape, since the erasure crate's own theorems about `next_chunk`,
  `add_chunk` and `message` carry `Usize.max` headroom preconditions the
  Braid cannot state through the opaque types (the Rust documents the
  constructible-but-unreachable overflow at `Decoder::new(usize::MAX)`);
  and the domain check `ValidateEkAgrees` does not see (under the Braid's KEM
  hypotheses, below). In the eight-leaf session unit the erasure coder is translated, so
  `DecoderMessageTotal` there is a statement about a definition. Stated for every decoder it was
  refuted (`Translation/SessionBraidReceiveVacuity.lean`); it is now stated for decoders that need at
  most `MAX_CODEWORDS` chunks, and the Braid receive theorems take that bound from the state
  (`State.decoders_bounded`). It is true given that `Vec::truncate` returns
  (`Translation/SessionBraidReceiveRepair.lean`). The statement is about the translation, whose
  `Vec::with_capacity` never fails, so it also covers a decoder with a small `needed` and a huge
  `size`, on which the Rust `Decoder::message` panics or aborts; `Decoder::invariant` rejects such a
  decoder through `needed == chunk_count(size)`, which `decoders_bounded` does not carry, and a Braid
  that passed `Braid::invariant` holds none. The other four erasure totals are proved in the session
  unit (`UnitSatisfiabilityErasure.lean`): `DecoderAddChunkTotal` and `EncoderNextChunkTotal` with no
  assumption about any opaque operation, `DecoderNewTotal` and `EncoderNewTotal` exactly when
  `usize::div_ceil` returns at divisor 32. The preservation theorems add `NewMsgLen` about the
  decoder (`BraidPreserveDecoder.lean`; see "The Braid's preservation theorems").

## Secret deletion is partial

The primitive boundary crate, `tacenta-core/boundary` (`tacenta-boundary`),
is part of this base since the session carve-out: it holds the X25519, AEAD,
ML-KEM-1024 and XEdDSA implementations the lifecycle calls, `attest.py`
lists it under the trusted primitive zones, and Charon leaves every one of
its functions opaque when it translates the lifecycle. Moving the code into
its own crate changed what is trusted by nothing: the same bodies were
trusted before behind `tacenta-core/src/primitives`.

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
  their buffer exactly before the first write, so they never grow, and so do
  the handshake's `km`, `kdf_sk` and `associated_data` in `tacenta-session`
  (CR-15). The sparse ratchet's, the Braid's and the Triple Ratchet's
  `to_bytes` now size their buffer exactly too, each from a length computed
  from the state and held to what is actually written by a
  `debug_assert_eq!`, as do the erasure coders' `to_bytes` the Braid embeds.
  One exception is worth naming: the Braid measures the two `tacenta-kem`
  values it carries by asking them for their bytes, because that crate
  exports no length constant for them, so a key pair's encoding is copied
  once into an exactly sized `Zeroizing` buffer that is wiped when it drops.
  That is a wiped copy in place of the unwiped ones a growing output buffer
  made. Every `Vec` inside libcrux is libcrux's.
  Two things about those exact sizings are worth stating plainly. The
  `debug_assert_eq!` holding each one is a development check, compiled out of
  a release build, so the shipping binary carries the sizing but not the check
  on it; Charon does not know that, and each assert arrives in the generated
  Lean as a `massert` the T1 proofs discharge. On those lines the Lean is
  stricter than the binary it was translated from -- the harmless direction,
  but not the same program.
  The classical ratchet’s skipped-key path now builds its working copy at the
  final capacity and wipes removed slots before shortening the vector. The sparse
  ratchet now does the same for skipped-key replacement and removal, derives new
  skipped keys directly into the final vector, rebuilds the chain table before
  growth, sizes its decoder vectors from the checked counts, and wipes old
  secret-bearing allocations before release. Its state destructor wipes the
  live fields as well.
  These are implementation hardening measures;
  Charon and Aeneas ignore `Drop` and allocator behaviour, so the proofs below
  do not establish them.

**None of it is proved.** Charon and Aeneas ignore `Drop` entirely, so the
generated Lean is byte for byte identical with and without every destructor
above, and no T1 or T3 theorem says anything about erasure. What guards part
of it is a static test that fails to build if a type loses the
`zeroize::ZeroizeOnDrop` marker, and the marker checks cover the classical ratchet's `State` and `SkippedKey`
(`the_state_erases_when_dropped`, `tacenta-core/ratchet/src/lib.rs`), the sparse
ratchet's `State`, `Chain`, `Chains` and `Skipped`, the ML-KEM `KeyPair`
(`the_key_pair_erases_when_dropped`, `tacenta-core/boundary/src/kem.rs`), and
`Identity` and `PrekeyStore` (`the_identity_and_the_prekey_store_erase_when_dropped`,
`tacenta-core/lifecycle/src/lifecycle.rs`). Each checks the marker, not what the
destructor wipes, and `KeyPair` and `PrekeyStore` implement the marker by hand.
The Braid's `Auth` and `Output`, and the KEM state it holds in `Zeroizing`
buffers, still need their own marker coverage; the Triple Ratchet's `State`
erases through the two ratchet states it holds. The sparse marker checks cover
the live state, but not transient allocator copies. Every marker check checks
the marker, not what the destructor wipes. Where a test exists it is a much
weaker instrument than the proofs standing next to it, and it should not be
mistaken for them. The Double Ratchet specification's own secure-deletion
section notes that recovering deleted data is platform-dependent and outside
its scope; the same caveat applies here. Treat forward secrecy as resting on the
key schedule, not on guaranteed erasure of every in-memory copy.

## Undefined behaviour: forbidden statically, checked dynamically where it can be

Every library crate in `tacenta-core` carries `#![forbid(unsafe_code)]`, except
that `tacenta-spqr` lifts it under the non-default `private-erasure-review`
feature. None contains `unsafe` in the default feature set, and the attribute is
what keeps that true rather than merely observed. One test target,
`tests/timing.rs`, has an `unsafe` inline-assembly block on aarch64 macOS. With
the non-default feature `private-erasure-review`, a second,
`tests/spqr_erasure_public.rs`, has `unsafe` allocator code (`ASSURANCE.md`,
practice 3). It bounds our own crates only; the primitives are the trusted
boundary and are unaffected.

`tooling/miri.sh` is the dynamic half. Miri interprets MIR and reports
undefined behaviour: out-of-bounds access, invalid aliasing, uninitialised
reads, misaligned pointers. With `unsafe` forbidden the interesting result is
not UB in our own unsafe code, which is limited to the items above, but that the *safe* code and
everything it calls in `core` and `alloc` executes cleanly, which catches an
`unsafe` block inside a dependency reached on one path, or a std API used in a
way that is unsound.

**Clean across `tacenta-protobuf`, `tacenta-kdf`, `tacenta-ratchet`,
`tacenta-session`, and `tacenta-triple`** (`tooling/miri.sh`), with no undefined
behaviour reported. For `tacenta-kdf` that run was of its RustCrypto wrapper; on the copied SHA-256, HMAC and
HKDF (ADR-0010) the crate's two unit tests pass under miri on one x86_64 Linux machine (2026-10-23), and the
workspace's 571 tests, clippy and fmt pass there. The first three run in seconds; `tacenta-triple`'s
conversation tests take minutes under the interpreter, so the script is meant to run
nightly rather than on every push. No workflow in this repository runs it, and the
date and commit of the last clean run are not recorded.

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
  X25519 and Ed25519 (dalek) are constant-time; ML-KEM (libcrux-ml-kem) is
  trusted, and its crate has a `check-secret-independence` feature that this
  build does not enable; the AEAD tag is checked
  with a constant-time comparison (`Mac::verify_slice`), not a byte-wise `==`.
  These properties are inherited from the crates, and assumed rather than
  re-established here.
- **The key derivation is copied code, held to a reviewed inventory of its compiled branches.** Since
  the KDF change (ADR-0010) `tacenta-kdf` is a SHA-256, an HMAC and an HKDF copied here (see the trust bullet above for
  who wrote and who has read it),
  whose comments say every branch and every index is on a length or a loop counter. They are loops, and this
  workspace's release profile adds an overflow check to every counter step, so they are not branch-free and the
  rule the gate applies to the two functions below cannot hold of them. `tooling/check-constant-time-asm.sh`
  instead lists every conditional branch of the crate's assembly, built in the release profile with one codegen
  unit (which the shipped build does not set), with the instruction before it, and every indirect transfer, table
  reference, register-indexed access, named callee and hardware divide, and requires the
  list to equal a baseline per target (`tooling/ct-baselines/`; CI compares the two Linux baselines, and the
  macOS one is compared only on a local run), whose items were read against the rule that each
  depends only on a length, a loop counter, the SHA-256 buffer's fill count, HKDF's block counter or position, or
  a constant (`tooling/ct-baselines/kdf-review-notes.txt`). That reading was made by a tool-assisted session, not
  a human reader. The baselines were read from one compiler, rustc 1.99.0-nightly (da80ed070), on an aarch64 Mac
  for its own target and, cross-compiled, for the two Linux targets. The gate builds this crate alone with the
  toolchain `tooling/ct-baselines/rust-toolchain.txt` names (`nightly-2026-07-15`) and first checks that the
  version rustup's `rustc` reports for it is the recorded one (`tooling/ct-baselines/rustc-version.txt`); on
  another it fails and names the compiler as the cause. That check reads the `rustc` proxy, so a `RUSTC`,
  `RUSTC_WRAPPER` or `build.rustc` override would bypass it and leave the exact comparison as the only check.
  Where the toolchain is not installed, a local run skips the KDF half with a line saying so; CI's `rust_target`
  step installs it and the run fails without it. The two straight-line functions below are read with the running
  toolchain, in CI the job's stable. Stable 1.98.1 gave the same inventory on the Mac. On one x86_64 Linux machine
  (an Intel CPU with SHA extensions, measured on 2026-10-23 by a tool-assisted session), the inventory built natively
  under the pinned nightly is byte-identical to the committed x86_64 baseline (122 items, read from cross-compiled
  assembly), and the shipped default codegen units gave the same; stable 1.99.1 there gives 127 items, the
  differences all in `Sha256::finalize` and `hkdf_sha256_into` and, by that session's reading, on lengths, counts
  and positions only, so the pin matters. A dudect-style test of the copied `hmac_sha256`
  (32-byte key, 64-byte message, 5.1 million measurements per class, one core, turbo off) detected no timing
  difference, while a control with a few extra instructions on a secret condition was detected. That is a tripwire
  and one measurement on one CPU, not a proof: no other CPU model, core type or frequency setting, no aarch64 Linux
  hardware and no phone was measured. The reader does not list an address computed into a register before it is
  used, and an LTO build, which would inline these functions into their callers, is not covered.
- **The Braid's MAC comparison is a hand-written loop.** `mac_eq` in
  `tacenta-braid` ORs the XOR of every byte pair and tests the accumulator
  once at the end -- the textbook shape -- but nothing in the language stops
  a compiler from recognising the shape and shortening it, and the crate
  carries no `subtle` because every dependency it has is a translation
  boundary. Moving the comparison behind an opaque boundary crate, where
  `subtle::ConstantTimeEq` is available and the translation sees an opaque
  call, changes the translated source and so waits for the next
  re-translation window. (This passage named the `kdf` crate for it; since
  the KDF change (ADR-0010) that crate is translated and has no dependencies, so it is no
  longer such a boundary.) Until then the guarantee is the loop's shape and
  `tooling/check-constant-time-asm.sh`, which CI runs: it reads the body of
  `mac_eq` in the release assembly built by the running toolchain (in CI, the
  job's stable) on the host and on the x86_64 and aarch64 Linux targets, from its label to its `.cfi_endproc`, and fails on any
  conditional-branch mnemonic or indirect jump in that body beyond the
  public length compare, and on any call out of it (the function calls
  nothing today; a `memcmp` appearing there would be the short-circuit the
  gate exists to catch). It inspects that one function and the names of its
  callees, not the callees' bodies. Today LLVM specialises the loop on the
  32-byte length and vectorises it, and the gate counts zero data-dependent
  branches and zero callees on every target.
- **The erasure code's field arithmetic branches on its data, and every
  operand on that path is public.** `gf::clmul`, `gf::reduce`, `gf::pow` and
  `gf::inv` in `tacenta-erasure` (`erasure/src/lib.rs`) test bits of their
  arguments and branch on them: the multiply scans the multiplier's bits, the
  reduction folds bit by bit from the top, exponentiation scans the exponent,
  and inversion special-cases zero. What reaches them is the lanes of the
  messages the Braid erasure-codes -- the KEM header with its MAC, `ct1`, the
  `ek` vector, and `ct2` with its MAC -- and the codeword indices, all of
  which travel on the wire, plus the constant exponent `65534` that `inv` is
  the only caller of `pow` with. No key, shared secret or decapsulation
  output reaches the coder. So the arithmetic is data-dependent in time and
  the data it depends on is public. It is recorded here rather than changed:
  a branch-free field would be a new translation and a re-proof of
  `ErasureT3.lean`'s `mul_refines`, for no attacker-visible gain.
- **XEdDSA: `verify` handles no secret, and `sign` has one conditional the
  timing harness cannot see.** `verify` in `primitives/xeddsa.rs` takes a
  public key, a message and a signature, all public, and its canonicality
  check on `u` is a plain comparison over them. `sign` derives the signing
  scalar in `calculate_key_pair`, which negates it under a `subtle::Choice`
  built from the Edwards sign bit (`conditional_negate`, a constant-time
  selection rather than a branch); that bit is one bit of the private key.
  Whether the compiled code keeps it branch-free is not a question
  `tests/timing.rs` can settle: the harness does not time XEdDSA (it times
  `aead::decrypt`'s rejection path and the tag comparison inside it), and
  one conditional negation inside a full scalar multiplication is not an
  effect its median-gap gate is built to resolve. It is instead settled, as
  far as it can be, by `tooling/check-constant-time-asm.sh`, which reads the
  body of `calculate_key_pair` (and `mac_eq`) in the release assembly on
  three targets and fails on any conditional-branch mnemonic or indirect
  jump in it. What it inspects is that one function's instructions and the
  names of the functions it calls, one level down: it prints the callee
  set, fails on a callee whose symbol names `subtle` (other than
  `subtle::black_box`) or `conditional_` -- the shape an outlined
  constant-time select would take -- and on any callee outside the set seen
  today (`Scalar`'s negation, `mul_base`, `compress`,
  `from_bytes_mod_order`, `black_box`, `zeroize`, `drop_in_place`, and the
  unwind pair). It does not read the callees' bodies: that the dalek scalar
  and point operations are branch-free is inherited from that crate, as the
  first bullet says of the whole trusted boundary. Adding the gate found
  one branch: with the workspace's overflow checks on, `subtle`'s mask
  negation compiled to a checked negation with a never-taken branch into a
  panic block. `subtle` is now compiled without overflow checks in this
  workspace's release profile (`tacenta-core/Cargo.toml`), and the function
  counts zero branches on every target.
- **Our own composition was read by the maintainer for leaks; no one independent has audited it.** tacenta-core's
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
- **Four of the claims above are measured by `tests/timing.rs`, not only read.** Those tests are `#[ignore]`d; they run by hand or in a nightly workflow of a private repository (see the timing section), and no workflow in this repository runs them.
  `tacenta-core/tests/timing.rs` times two input classes and asks whether their
  rejection times differ by an *exploitable* margin -- an effect size in
  nanoseconds. Besides the AEAD tag comparison and the forged-ciphertext
  path it now times the Braid's header MAC path and the whole
  `Session::decrypt` rejection path; those two are microsecond-scale
  operations, gated on a two-percent relative floor whose resolution the
  test file states (it resolves different work by class, not a ten-nanosecond
  short-circuit, which is the assembly gate's job). Representative results
  follow, in two parts that do not come from the same machine.

  The first two rows are from the nightly run on the dedicated machine's
  isolated measurement core and carry no stamp: no commit, date, hardware or
  run identifier was recorded with them, so a reader cannot tell which build
  produced them or how old they are. `tests/timing.rs` now prints a
  provenance header at the start of every run (commit, date, `rustc`
  version, the command line, rounds × samples) to the test's captured
  output, where it is visible with `--nocapture` (the invocation the file's
  own usage line gives) and not otherwise, and the nightly job is to add the
  fields only the machine knows -- CPU model and its fixed frequency, the
  isolated core, a run id -- after which these two rows are replaced by a
  stamped run:

  | What | Class A median | Class B median | effect size | leak floor |
  | --- | --- | --- | --- | --- |
  | Tag comparison, by how much of the tag was right | wrong at byte 0: 213 ns | wrong at byte 31: 215 ns | 2 ns | 5 ns |
  | Rejection, by forged ciphertext contents | all-zero: 261 ns | all-ones: 263 ns | 2 ns | 5 ns |

  The classes differ by ~2 ns -- the integer-nanosecond timer's quantization
  floor -- against a 5 ns leak floor. A byte-wise `==` that short-circuited on the
  first wrong byte would differ by ~10 ns, and an attacker who saw that would
  recover a tag one byte at a time; the constant-time `Mac::verify_slice` does not.

  The next two rows are the two microsecond-scale tests, and they are
  **local screening numbers, not the nightly's**: one release run on a
  developer machine, not on an isolated core at a fixed clock, taken to show
  the scale each floor sits at and nothing finer. They carry the stamp the
  test printed -- commit `687b248e4e0a5abd5f5b2ba6cca2939a770364dc`, date
  `2026-09-09T13:35:17Z`, `rustc 1.96.0-nightly (562dee482 2026-03-21)`,
  plan 11 rounds × 4000 samples per class, run with `--test-threads=1` --
  on an `aarch64-apple-darwin` host (the target `rustc -vV` reports; the
  stamp has no CPU field, so no model is recorded here). The timer on that
  host has a 41.67 ns quantum, which is why the medians land on multiples
  of it:

  | What | Class A median | Class B median | effect size | leak floor |
  | --- | --- | --- | --- | --- |
  | Braid header MAC, by how much of the MAC was right | 2,625 ns | 2,625 ns | 0 ns | 52.5 ns (2 %) |
  | `Session::decrypt` rejection, by how much of the tag was right | 107,750 ns | 107,875 ns | 125 ns | 2,155 ns (2 %) |

  Read against what the test file says the floors resolve: the Braid floor
  of ~50 ns sits below the cost of one skipped HMAC, so a MAC skipped on one
  side would show; the session floor of ~2 µs does not, and would show only
  an omitted agreement-scale step (a Diffie-Hellman, a KEM operation, a
  state clone). The 125 ns session gap is three timer quanta on a path that
  allocates and walks kilobytes of state, the allocator-and-cache drift the
  test file describes for two interleaved classes on a shared machine; the
  nightly's numbers on the isolated core are the ones to hold the claim to.

  **This raises those two from assumed to measured, not to proven.** A measurement
  covers the inputs it draws on the machine it runs on; a proof covers all of
  them. What it buys is that a regression becomes visible, which reading the code
  cannot. The tests are `#[ignore]`d out of the per-push run and run nightly in
  release mode by a nightly timing workflow, which lives in
  `tacenta-core-private-backup`, this repository's private predecessor -- not
  here, and not in the deployment repository. **That workflow checks out its own
  tree**, so it runs that repository's copy of `tests/timing.rs`, not this one:
  until a change here is mirrored there, no scheduled job runs it. Run them by hand with
  `cargo test --release --test timing -- --ignored --nocapture`, from
  `tacenta-core/` (the `-p` form fails from the repository root, and without
  `--release` the numbers are a debug build's, not the ones described here).

  **The harness carries three calibration controls, and they are load-bearing.**
  Every leak assertion here is a negative result, and a negative result is
  evidence only from an instrument that would have reported the positive. So the
  same measurement, floors and statistics are run over deliberately leaky
  stand-ins -- a byte-at-a-time tag comparison, a rejection path costing a few
  per cent more on one class of a microsecond path, and a leak confined to the
  first rejection after the class changes -- and the controls fail if the leak
  is *not* detected. Each names the batch factor it must be caught at, so each
  pins one leg of the measurement rather than leaving the other free. A failing control does not mean this codebase leaks; it means the
  harness has gone blind, and that the other results are not evidence until it
  is understood.

  **What the first control found, on its first run.** The absolute floor is
  5 ns, and `Instant`'s resolution is a property of the host: on Apple Silicon
  it is 41.67 ns (a 24 MHz timebase; measured, not assumed -- the smallest
  non-zero deltas it reports are 41, 42, 83, 84, 125, 166 ns). Timing one
  rejection at a time, a median gap can then only read 0 or >= 41.67 ns, so a
  5 ns floor was never a 5 ns floor there. The ~10 ns byte-at-a-time
  short-circuit these tests exist to catch fell underneath the quantum and
  measured as **exactly 0.00 ns** -- an indistinguishable-looking pass from a
  harness that could not have distinguished anything. The nightly job runs on an
  isolated linux x64 core with a far finer timer, so the gate was sound where it
  gates; every run anywhere else silently was not. **Any previously recorded
  0.00 ns separation from an Apple Silicon host should be read in that light,
  including one taken during external review, the aarch64 rows in the screening
  table above, and the `0 ns on a DIT core` that `EFFECT_FLOOR_NS`'s own
  derivation rests on.** A non-zero unbatched reading is no better: at a
  41.67 ns quantum a 12 ns difference reads as 0 or as one whole tick, so such a
  number is "same tick" or "different tick", not an effect size.

  The fix is in `Floor::batch`: measure the host's quantum and time enough
  rejections per sample that `quantum / batch` sits at half the floor or better,
  dividing the sample count by the same factor so the total work is the same to
  within one batch.
  On a nanosecond-resolution host the factor is 1 and nothing changes; on Apple
  Silicon it is 17, and the same short-circuit then measures 12--13 ns against a
  real path's 0.00--0.06 ns.

  **Each control makes up to three attempts and needs one detection.** That is a
  retry, and gates here are never retried: re-running a gate until it passes is
  how a real leak ships. A control is the other direction, and the failure it
  exists to catch -- a blind harness -- is systematic rather than stochastic,
  so three attempts fail as surely as one; deleting the batching leaves the
  effect at 0.00 ns on every attempt. What the retry removes is the quantized
  draw, which reddened a working harness about one run in twenty-five.

  **What the controls do not establish, listed because a list of controls reads
  as coverage.** No control pins the sampling plan: `LEAK_ROUNDS` and
  `LEAK_SAMPLES` can be cut a hundredfold and the controls stay green. That is
  not because the plan is spare -- thinning it makes the *real* tests go red on
  honest code, which is the failure a reader would meet first -- but because
  nothing here demonstrates either direction. Nor is the relative floor tightly
  pinned: it can be loosened about two and a half times, or inflated at the
  session scale alone, with every control green. And none of this runs on a
  schedule while the nightly checks out another tree.

  **Batching has a cost, and it is the other half of the same trade.** A batched
  sample averages, so a leak confined to the first rejection after the class
  changes -- a cold cache, a cold predictor -- is attenuated: one measured at
  42 ns unbatched read 7.3 ns at seventeen per sample, close enough to the 5 ns
  floor that a smaller one would vanish. Choosing a single factor therefore
  chooses which class of leak to be blind to, so the ordinary direction measures
  at **both** and a path must be indistinguishable at each. A third control, a
  stand-in that leaks only on that first rejection, fails if it stops doing so. A batched sample measures steady-state repeated
  rejection rather than a cold one, which is a real change to the question and
  is stated with the code.

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
  the same test measures what the bound permits. As with the table above,
  these numbers are from the nightly run on the dedicated machine and carry
  no stamp yet; the same provenance header covers them:

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
what it is not. `CLAIMS.md`, "Proved (tier T2, model-level security properties
against the symbolic attacker)", records each `Properties/` theorem this section
discusses, with its hypotheses and its pinned axioms. `Proofs.SessionEstablishment`,
which this section also names, is recorded in its own section there.

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
the chain key and the root key the next root step derives, unless it also took
that epoch's agreement output. The argument is the arity of the rule -- the
derivation needs both halves, and an agreement output is a leaf available only
to whoever took it. Both theorems are about that one step; neither carries to
the step after it.

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
and unavailable outside it. Sessions never share a key, and an attacker holding
one chain key of a session derives no chain key and no message key of a session
seeded differently. Without that, unforgeability would
hold and authentication would still fail, because a message made for one
conversation would verify in another.

Two things it does not cover. The identity binding in the associated data is
proved elsewhere, in `Proofs.SessionEstablishment`, and neither half suffices
alone. And nothing anywhere in this project proves that an identity key belongs to
the person a user means: that is trust on first use and the directory's problem,
and it is the assumption a user actually bears.

## Eight theorem-bearing zones on the shipping path; lifecycle is translated but unproved

**Read this before the list.** Integrating the Triple Ratchet
moved `Session::encrypt` and `Session::decrypt` off `tacenta-ratchet::send` and
onto `tacenta-triple`, which drives `tacenta-spqr` and `tacenta-braid`.

`tacenta-spqr` and `tacenta-braid` are **translated**, with no `sorry` and
no body Aeneas gave up on, so a change that breaks their translatability fails
the retranslation in the verification workflow rather than passing quietly.

**T1 covers all of `tacenta-spqr`'s protocol surface** (not the
persistence codecs `from_bytes`/`to_bytes` and their entry decoders, nor
`init`/`init_alice`/`init_bob`, `Output::new`, `epoch`, `skipped_len` or
`evict_oldest`, which are translated and have no theorem on this island (the
session unit's `UnitLifecycleT1.lean` proves `evict_oldest` panic-free under
`RemoveSkippedAtTotal`); see CLAIMS.md's
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

Two of them are no longer assumptions when the state came from
`State::from_bytes`. `Translation/ImportInv.lean` proves that a state the
translated `from_bytes` returns satisfies this crate's `invariant()`, and that
the invariant gives both of `receive_no_panic`'s preconditions outright:
`Spqr.inv_gives_chain_room` (the epoch window plus per-epoch distinctness bound
the chains vector at two entries, so `chains.length + 2 < usize::MAX` needs
nothing further) and `Spqr.inv_gives_skip_room` (2000 stored keys plus
`MAX_SKIP` is 3000). `Spqr.decoded_receive_no_panic` states the composition
with no side condition left over. It carries no compiler-trust
axiom: the one closed numeric fact it inherits from `SpqrT1.receive_no_panic` was
settled by `native_decide` until 2026-09-30 and is now settled by `decide`. It is
pinned under `#guard_msgs` in `ImportInv.lean`, and no statement in that file is
compiler-trusted. Three of the
refinement's premises come off the same invariant -- the two above, which are
also `SpqrT3.receive_refines`'s `hroom` and `hskiproom`, and `hone` -- but
five do not come off the invariant alone: `hepoch`, `hcb`, `hsb`, `hnewb` and
`hcounter` are not consequences of `invariant()`, and a state with
`epoch = u64::MAX - 1` and a chain at that epoch passes the invariant and fails
both `hepoch` and `hcb`. `hcb` and `hsb` do follow from the invariant together
with `hepoch` (`spqr_receive_premises` in `Translation/DecodedStateDischarge.lean`).
`hepoch` is on the list because `advance` now reserves `u64::MAX` and refuses
the step that would reach it, so the refinement asks for a step of headroom
(`epoch + 1 < u64::MAX`) while the invariant reaches only `epoch < u64::MAX`
(`Spqr.inv_gives_epoch_room`) and admits `epoch = u64::MAX - 1`, which is a
fully usable epoch the operations produce. So three of the five stay with the
caller, `hepoch`, `hnewb` and `hcounter`, and CLAIMS.md says so where the
theorems are listed.

**`tacenta-spqr` also has T3**: `send`/`receive` compute what
`Model.SparseRatchet.send`/`receive` say -- the key returned, the output
reported, and the state transitioned to -- across every branch each can
take, not merely that they cannot fail. Unlike the ML-KEM Braid this crate
has no KEM boundary and no erasure-coding boundary to assume agreement at;
the only call this file assumes anything about the *value* of is
`hkdf_sha256` (opaque until the KDF change (ADR-0010), a translated definition since; `SpqrHkdfAgrees` is still the
hypothesis here, and `KdfLeafAgreements.spqr_hkdfAgrees` proves it of this translation's KDF). `Vec::pop`, `Vec::capacity`, `Zeroize` and `Option::clone` are opaque too, each its own
assumption below, and the retain and removal scans are translated loops whose results the file assumes
(`VecRetainAgrees` and `RemoveSkippedAtAgrees`, from the boundary stated below). `find_chains` is proved
outright. `set_chains` and `clear_old_epochs` are `VecRetainAgrees` applied to its arguments, and
`advance`/`maybe_advance`, `try_skipped` and `skip_message_keys` are proved under it and
`RemoveSkippedAtAgrees`.
`Model.SparseRatchet.lean` carries its own lemma library, as `Model.Braid.lean`
does: how far `advance` can shrink the skipped-key store,
how a chain-vector length bound survives `set_chains`/`skip_message_keys`,
and a left-peeling split for the forward-derivation walk `skip_message_keys`
performs. Eight assumptions back it: `SpqrHkdfAgrees` (one level below
`SpqrT1.lean`'s `KdfRkTotal`/`KdfCkTotal`, subsuming both), `VecRetainAgrees`
and `RemoveSkippedAtAgrees` (each strictly stronger than its `SpqrT1.lean`
namesake), `SpqrT1.VecRetainTotal` (carried from `SpqrT1.lean`, for the capacity and wipe calls the
retain agreement does not cover),
`ZeroizingRoundTrips96` and `ZeroizingRoundTrips64` (the key derivation's
outputs are wrapped in `Zeroizing` since CR-15, and the wrapper's `new` and
`deref` are opaque to the translation, so each width needs the round trip
stated; `Satisfiability.lean` exhibits a model of each), and
`Tacenta.SpqrT1.ZeroizeTotal`/`OptionCloneTotal` carried over unchanged. See
`SpqrT3.lean`'s own closing section and `CLAIMS.md`'s spqr T3 entry for the
full account.

**The `hcounter` precondition is scoped to the input state's own chains
table.** `send_refines`/`receive_refines` (`SpqrT3.lean`) each carry an
`hcounter` hypothesis saying "the chain this call is about to step forward
has not yet sent 2^64 messages", and an `hepoch` saying the epoch has a step
of room left below `u64::MAX` (`epoch + 1 < u64::MAX`: `advance` reserves the
ceiling and refuses the step that would reach it, and the model refuses it
too, but with a `none` that `advance_refines` reads as the mismatch refusal,
so at `epoch = u64::MAX - 1` that theorem's correspondence fails);
`SpqrT1.lean`'s `send_no_panic`/`receive_no_panic` carry neither any more
(below). It is stated over the real input state's own chains
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
carry an existing counter through or open a fresh one at zero). The
precondition is one every real caller satisfies.

**`SpqrT1.lean`'s `advance_no_panic`, `maybe_advance_no_panic`,
`send_no_panic` and `receive_no_panic` carry no `hepoch` and no
`hcounter`.** Every increment of the epoch (`advance`) and of a chain's
message counter (`send`, `receive`) is a `checked_add` in the source, whose
`None` arm is a returned `ChainExhausted` with the state untouched, and the
four proofs walk that arm as a value rather than assume it away -- the same
move `BraidT1.lean` made for the Braid's epoch with CR-03. The membership
clauses that `VecRetainTotal`, `find_chains_no_panic`,
`set_chains_no_panic`, `clear_old_epochs_no_panic`, `advance_no_panic`,
`maybe_advance_no_panic` and `skip_message_keys_no_panic` carry were
introduced so the earlier `hcounter` could reach the chain it was about;
they stay, being true of the code and what a caller reasoning about the
table's contents needs. `SpqrT3.lean` keeps both bounds. They were kept for
the model's reason rather than the code's, when `Model.SparseRatchet` counted
in `Nat` and the code's `ChainExhausted` had nothing to refine against. The
model now refuses at both ceilings -- the advance onto epoch `u64::MAX`, and a
send past a chain's counter at `u64::MAX`. `send_refines` and
`receive_refines` take any error in their failure clauses, so they may no
longer need either bound; `advance_refines`, whose failure clause names
`EpochOutOfOrder`, does need `hepoch`, and the proofs use both bounds to refute
the exhaustion branches. Whether the two could be dropped from the top-level
theorems has not been checked, and they are kept. `BraidT3.lean` keeps
its `hepoch` where `BraidT1.lean` dropped it, on the same terms: it was kept
because `Model.Braid` counted epochs in `Nat`, and the model now refuses the
step onto epoch `u64::MAX` in transitions (5) and (13), as the code does.
Whether `hepoch` could be dropped from `step_receive_refines` and
`Braid.receive_refines` has not been checked. The Triple Ratchet's refinement keeps them too, through its sparse
bundle, at the reserved ceiling's `epoch + 1 < u64::MAX`. On the three-leaf unit
that bundle is proved from `UnitSpqrT3.lean`'s theorems, so a clause asking less
than they need would not build. While the bundle was only assumed, on the Triple
translated alone, it drifted from the leaves once.

**`tacenta-triple` has T3, against a composed model of its own.**
`Model.TripleRatchet.lean` carries `splitSecret`/`combine`, the two
KDF calls this composition makes on its own (opaque until the KDF change (ADR-0010)); `Model.Triple.lean` is
the composed `State`/`send`/`receive`/`commit` state machine, mirroring the
real crate's clone-candidate-commit shape (`receive` returns a candidate
state without mutating its input; `commit` is a separate, near-trivial step,
so that state never advances on an unauthenticated message).

**Its T3 is proved on the three-leaf unit, and its history explains the
shape.** On the Triple translated on its own, both inner states were bare opaque
axioms and the inner ratchets' own refinement theorems could not be imported
beside it, so the proof about that translation, `TripleT3.lean`, had to assume
two hand-written bundles, `RatchetAgreesFor`/`SpqrAgreesFor`: an abstraction under
which `clone`, both initialisers, the small accessors, `send` and `receive` agree
with the model. They were stronger than the leaves, carrying none of their
boundary hypotheses, and held to the leaf theorems by eye and by a textual drift
checker. `Translation/UnitTripleT3.lean` states the same theorems on the unit,
where the inner states are concrete, and proves both bundles from the unit's
copies of the inner refinements; the standalone translation, `TripleT3.lean` and
the checker were deleted after 2a89a7f. What remains assumed is the inner
refinements' own boundary, stated explicitly; "The Triple's refinement is on the
unit" below gives the details.

**`receive_refines` claims the success case only, and that traces back to
`T3.lean`'s own claim, not a new gap.** `Translation/T3.lean`'s
`receive_refines` for the classical ratchet states no failure-branch fact at
all, so there is nothing for `UnitTripleT3.lean`'s `receive_refines` to
compose a triple-level failure claim from.

**`send_refines`'s failure branch states the exact refusal on both ratchets.**
`RatchetAgreesFor`'s and `SpqrAgreesFor`'s send clauses state, for every error
the inner send returns, the detailed model refusal it corresponds to
(`sendRefusalOfReal`), matching `Translation/T3.lean`'s and
`Translation/SpqrT3.lean`'s own `send_refines`, which now prove that for every
error: on the classical side `NoSendingChain` and `ChainExhausted`, the real
`u32` send counter's exhaustion at `ns = u32::MAX`. The composed
`send_refines` states the Triple refusal for every error. Earlier the classical
clause covered `NoSendingChain` only, because `T3.lean` proved nothing about
`ChainExhausted`; that gap is closed by the stronger leaf statement, not by a
wider hypothesis.
`SpqrAgreesFor`'s analogous clause is unconditional and genuinely holds:
`hcounter` already rules out the post-quantum counter's own exhaustion.

The one primitive `split_secret`/`combine` call that is not the two
ratchets' public calling surface is `hkdf_sha256` (opaque until the KDF change (ADR-0010), a translated definition
since). Its agreement,
`TripleHkdfAgrees`, is on the unit the same proposition as the classical
ratchet's `HkdfAgrees`.

**`tacenta-braid` has T1 for its whole public surface, not just its one
loop.** The eleven-state machine's `step_send` and `step_receive`, their entry
points `send`, `receive` and `commit`, and every helper the state machine
calls are proved panic-free, alongside the constant-time authenticator
comparison that is this crate's only loop. `step_receive` is the one an
attacker's header, chunk data and claimed lengths drive directly, so this is
what stands between a malformed message and a remote denial of service for
this leaf crate. One real precondition travels with it: a concrete size cap on
the KEM ciphertext carried across the encapsulation exchange. `step_send` and
`step_receive` each make a `ct1`, so neither keeps the cap alone, and this file
does not prove it is kept, since that would be a T3 claim about the whole state
machine rather than a T1 one about a single function. `BraidPreserve.lean`
proves that `State.sized`, which gives it, is kept by every successful step. The
epoch counter below `2^64` it used to need as well, the same
shape of bound the classical ratchet and the sparse ratchet each need for
their own counters, is no longer a hypothesis: the two transitions that
advance the epoch use `checked_add` and answer `Failed` at the ceiling
(CR-03), which the theorems prove as a value.

That size cap is discharged for a decoded Braid.
`Translation/ImportInv.lean` proves that a Braid the translated
`Braid::from_bytes` returns is one its `invariant()` accepted, and that the
invariant's per-state `ct1.len() == CT1_LEN` clauses give
`State.ct1_bounded` (`Braid.invariant_true_gives_inv`), so
`Braid.decoded_receive_no_panic` states panic-freedom of `receive` on a decoded
Braid with no state-shaped side condition. It rests on `Ct1LenTotal`, which
`BraidT1.lean` already states and uses: `tacenta_kem::CT1_LEN` returns a value
at most 4096, and the real constant is 1408. Only that clause is derived --
the rest of the Braid's `invariant()` delegates to `tacenta-erasure`'s coder
invariants, which reach this translation as opaque axioms -- and
`BraidT3.step_receive_refines`'s `epoch + 1 < u64::MAX` is not among the
invariant's clauses at all (it bounds the epoch only from below,
`epoch >= 1`), so it stays with the caller.

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
exclude such a `K` through `KemLenAgrees` and `HonestChunk`; nothing in the
operation-agreement clauses does, and a whole-run composition of the Braid
theorems would need size laws on `K` (`hashEk` output 32 bytes, `keyGen` seed 32 bytes,
`encaps1`'s `ct1` of `ct1Size`, and so on) that the model does not state --
an open item, not a falsity. And the KEM agreements are guarded by the
lengths the real crate checks (`decapsulate` on `ct1Size`/`ct2Size`,
`encapsulate1` on the 64-byte header, `encapsulate2` on `ekSize`, and
`validate_ek` on a 32-byte seed, a 32-byte hash and an `ekSize` vector);
stated for every slice they would claim success where the crate returns an
error, which is what `ValidateEkAgrees` did until its length premises were
added (below).

**`KemAgreesFor`'s encapsulation clause binds the model's randomness
existentially per RNG state, as its key-generation clause does; an earlier
revision's did not, and admitted no real KEM.** Real ML-KEM encapsulation
draws 32 random bytes and returns a different `(ct1, ss)` pair under a
different RNG state. `Model.Braid.Kem.encaps1` now takes that randomness
(`encaps1 : Nat → Bytes → Bytes → …`), and `Model.Braid.send K rand` passes
its `rand` to transition (7)'s encapsulation as it already did to transition (1)'s key
generation, and the clause reads `∃ rng' rand', (∃ es ct1raw ssraw, encapsulate1
… = ok (Ok (es, ct1raw, ssraw), rng') ∧ … K.encaps1 rand' ekSeed hek = some …) ∨
((∃ e, encapsulate1 … = ok (Err e, rng')) ∧ … K.encaps1 rand' ekSeed hek = none)`:
for each RNG state, *some* model randomness makes the model's answer the real
one, success or refusal, which is all a proof that does not control the RNG
can say, and is what the key-generation clause (`∃ rng' rand`, with the same
two arms inside) always said about the success side. `step_send_refines`
and `Braid.send_refines` choose that `rand'` as the `rand` their conclusion
binds. `Model.Braid.receive` needed no randomness argument: no receive
transition encapsulates (transitions 9, 11 and 12 finish an encapsulation
with `encaps2`, which is deterministic given the encapsulation state), so
`step_receive_refines` and `Braid.receive_refines` changed statement only
through `KemAgreesFor` itself. Until this revision the clause fixed one pair
per header for every RNG state, a function of the header alone; the only
implementation that satisfied it was the derandomised `toyKem` of
`Translation/KemWitness.lean`, and the four Braid refinement theorems
described a Braid over a derandomised KEM. `toyKem.encaps1` still ignores
its randomness, which is now a legitimate model of the clause (a KEM that
draws no randomness satisfies "some randomness makes the model agree" with
any value), and the witness picks `0`. What the two randomness-drawing
clauses assume beyond agreement is `BraidT1.RngTotal rc`: that the caller's
`fill_bytes` returns, which the real `generate`/`encapsulate1` need. A former
`K.Correct` conjunct asked that decapsulation recover the secret for *every*
pair of randomness values, while ML-KEM-1024 is δ-correct with the
decapsulation-failure probability bounded by FIPS 203. Neither refinement
proof used that conjunct: both destructured and discarded it. It is now
removed from `KemAgreesFor`, so the four Braid refinement theorems no longer
assume a property false of the shipped KEM. Since the model's KEM operations
return `Option` (mlkem-braid.md, Failure), every clause of `KemAgreesFor`,
`KeyPairRefines` and `EncapsRefines` is two-sided: the real call and the model
answer alike, `Ok` with `some` of the same bytes or `Err` with `none`. The four
real `Err` arms are refined against the model's `Failed` transitions, and no
clause says the real KEM never refuses. The witnesses at `toyKem` take only the
success arms, so no witness exercises a refusal arm, and no vector does either:
the vector generator has only `toyKem`, which never refuses, and the vector
format has no field that makes a call refuse, so the four arms are checked
against the Rust by the refinement proofs, under `KemAgreesFor`, and against
the model by nothing a vector carries. The independent reader drives its own KEM to refuse (its case
BR-12) and tests the four arms against its reading of the specification, not
against the model. That the real wrapper does refuse, and when, is not shown
here in Lean. By test it refuses one known class of input: a restored
encapsulation state with an out-of-bound coefficient (the section on the
Session unit's primitive contracts below, and `KEM-STORED-STATE-TOTALITY` in
the gap register). The model can express that refusal as `encaps2` returning
`none` at that state, and `finish_encaps_refines` refines the real `Err` arm
under `EncapsRefines` for the state; no theorem relates a restored Braid to a
model state, so nothing supplies that hypothesis for a tampered store, no `K`
in the tree refuses, and the coefficient rule is not modelled.
`Model.Braid.toyKem_correct`
remains a fact about the toy model rather than a boundary premise. The
definition's former `∀ kp` clause -- that *every* `IncrementalKeyPair`
decodes as some `dk`, `ekSeed` and `ekVector` whose header is `ekSeed ++
hashEk ekSeed ekVector` -- was applied by no proof in `BraidT3.lean` and is
false of the real type (`IncrementalKeyPair::from_bytes` checks only the
length of its input), and has been deleted. What remains is
`ValidateEkAgrees`, taken by `step_receive_refines` and
`Braid.receive_refines`, states that `validate_ek` accepts exactly when the
model's `hashEk` recomputation matches the stored hash, for a 32-byte seed,
a 32-byte hash and a vector of `ekSize` bytes. The three length premises
are what the crate checks first: libcrux's `validate_pk_bytes` returns
`Err`, so `validate_ek` returns `false`, on a header or vector of the wrong
length before it hashes anything. Without them -- as the hypothesis stood
before this revision, for a `hek` and `ekVector` of any length -- it was
false of the real `validate_ek` for every `K`, not, as this ledger said,
satisfiable by a suitable `hashEk`: with `ekVector := []` and `hek :=
K.hashEk ekSeed []` the clause demanded `true` where the crate answers
`false`. With the lengths fixed, what remains is the domain check:
`validate_pk_bytes` also checks the vector's coefficients after the hash
comparison, so the agreement holds of the real operation only for a
`hashEk` that folds that check into its result, which the documented hash
does not.

**What `validate_ek` covers is the public half only.** The check is FIPS 203's
`H(ek)`: it recomputes the hash of the encapsulation key embedded in the
header and compares it with the stored hash. That binds the header to that
public key and says nothing about the decapsulation key stored beside it. The
private half is **not verified anywhere in this tree, and about half of it
cannot be**: the secret polynomial vector carries no redundancy in the
encoding to check it against, so no amount of decoding validates it, and
`IncrementalKeyPair::from_bytes` checks only its input's length (above). The
Braid's reader does apply `validate_ek` to a stored pair (register item J-4):
`Braid::invariant`, which `Braid::from_bytes` refuses on, requires in the four
states that hold a pair that the pair's own header and `ek_vector` pass it.
So a stored pair whose header hash is not the hash of its own encapsulation
key, or whose `ek_vector` has a coefficient at or above q, is refused as
malformed at import. That reaches the public half again and nothing more, and
it trusts libcrux's `validate_pk_bytes` to accept every pair libcrux
generates: were it to refuse one, the reader would refuse a state this crate
exported. Nothing proves that; the crate's tests check it after every step of
the negotiations they run. A stored key pair whose private half has been
altered still passes every check that is made and fails only when
decapsulation produces the wrong secret. Nothing in `BraidT3.lean` --
`ValidateEkAgrees` included -- states otherwise.

Two more sit beside it in `BraidT3.lean`: `KemCloneAgrees` and
`ErasureCloneAgrees` (a clone of an opaque KEM or erasure value behaves as,
respectively is, the original), hypotheses of `Braid.receive_refines` and
`State.clone_refines`. Each is the same shape of boundary fact as the KDF
agreements. `KemCloneAgrees` covers the whole `Result` of `decapsulate` and
`encapsulate2`: a clone refuses where its original refuses, which the
two-sided `KeyPairRefines` and `EncapsRefines` need to carry a refusal across
`State.clone`.

**An assumption is per translated crate, not per operation.** An earlier revision
listed `VecRemoveTotal` once below, and there were two: each translation unit declared its own
opaque `alloc.vec.Vec.remove`. The translations no longer call `Vec::remove`, and the removal
helpers' hypotheses (`T1.RemoveSkippedAtTotal`, `SpqrT1.RemoveSkippedAtTotal`) are about translated
functions; the point survives in the laws they follow from, since each translation unit declares
its own opaque `alloc.vec.Vec.pop`, so the classical ratchet's `LawPop` and the sparse ratchet's
are about *different constants* and neither discharges the other
(`SatisfiabilityRatchetLaws.lean` states it again). One modelling gap in Aeneas becomes one
assumption per crate that touches it. Anyone counting the trusted base by name
rather than by constant will undercount.

`VecRetainTotal` and `KdfRkTotal` join them. `VecRetainTotal` carries a length
clause as well as totality, because `set_chains` pushes after retaining and
without knowing the retain did not grow the vector there is nothing to bound the
push against.

`KdfCkTotal` and `ZeroizeTotal` are there for the same reason: the sparse
ratchet's chain-key derivation bottoms out in its own copy of
`hkdf_sha256` (opaque until the KDF change (ADR-0010), a translated definition since), and its buffer wipe in its own copy of the `Zeroize` blanket
implementation. `send` and `receive` need two more:
`OptionCloneTotal`, since both functions clone the *other* direction's chain
through an `Option`, which has no clone specification in Aeneas's own library;
and `VecAppendTotal`, which is `True` now that `skip_message_keys` derives into its final vector and no
longer calls `Vec::append`, and is kept as a name for the downstream files. **Seven assumptions in
that one file, none of them the same proposition as its namesake elsewhere.**

**So both `tacenta-spqr` and `tacenta-braid` are fully covered by T1.**
`tacenta-braid` alone assumes twenty-six named constants over twenty-six
distinct operations -- the erasure coder, the KEM, the two KDF calls (opaque until
the KDF change (ADR-0010), translated definitions since, with their hypotheses kept),
`Option::clone`, and since CR-15 the `zeroize` crate's wrapper round trip,
its in-place wipe of a fixed-size array and the `RangeFull` slice index
(`ZeroizingArrayRoundTrip`, `ArrayZeroizeTotal`, `RangeFullIndexTotal`,
each with a model in `Satisfiability.lean`) -- each a per-crate axiom Aeneas
could not model, none shared with any other crate's copy of the same
operation. Several carry a
concrete size cap rather than mere headroom below `Usize.max`, because more
than one capped value gets summed at a single call site and two facts each
individually "under `Usize.max`" do not compose the way two concrete small
caps do.

**Two leaf crates proved is not the whole agreement**, since `tacenta-triple`
is the crate that actually composes them with the classical ratchet.

**`tacenta-triple` is translated inside the three-leaf unit, and carries its T1
proofs there.** `run-aeneas.sh` does not translate it on its own; it translates
`tacenta-core/triple-unit`, the Triple and both inner ratchets compiled as one
crate ("The three-leaf translation unit" below), which carries no `sorry` and no
body Aeneas gave up on, the same bar the rest of this list holds to.

**Translated is mostly proved.** `State.send`, `State.receive`,
`State.commit`, the two constructors, the clone, the accessors,
`split_secret` and `combine` carry T1 theorems (`UnitTripleT1.lean`), and so do
`classical_skipped_len`, `post_quantum_skipped_len` and
`post_quantum_receive_count`. Four public functions do not:
`evict_oldest_classical`, `evict_oldest_post_quantum`, `to_bytes` and
`from_bytes`, and the session calls all four, from its eviction loop and its
persistence path. On the eight-leaf session unit the two eviction functions
now carry T1 theorems (`UnitLifecycleT1.lean`, under `RemoveSkippedAtTotal`
and `ZeroizeTotal`); the codecs still have none
(`tacenta-core/lifecycle/src/lifecycle.rs`). Neither the classical ratchet's own
`receive_no_panic` nor the sparse ratchet's `send_no_panic`/`receive_no_panic`
said anything about what happens when the two are composed, and the
composition is what ships since the triple-ratchet integration -- this is that composition's
own proof. It carries four preconditions, all about the inner ratchets' sizes,
and they land on the unproved session layer ("Four preconditions land
outside the translated tree" below).

**The gap the standalone proof had is closed on the unit.** Proved about the
Triple translated on its own, the same theorems rested on seventeen
unconditional totality bundles about the inner ratchets, stronger than any leaf
theorem and several about operations no leaf file proved anything about. The
unit proves all seventeen under the leaves' real preconditions, and that
standalone proof was deleted after 2a89a7f.

**So the session's send and receive path has a claim resting under it, at
the crate that actually carries it.** `Session::encrypt` and
`Session::decrypt` themselves live in `tacenta-core/lifecycle/src`, the product
code that calls `tacenta-triple`. The Phase 0 lifecycle translation now covers
that code. On the eight-leaf session unit it has five conditional panic-freedom
theorems, all conditional on records that are inhabited only in the sense of "The four contract records follow from an axiom base that has a model, under five laws" (three of them on a record that had a false field
until it was restated; `GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`), and one lemma (`CLAIMS.md`, the session lifecycle T1 section) and no
theorem that relates it to the model -- a separate question this does not
answer.

The proof tiers cover **eight** leaf crates, and a claim that names only the
ratchet understates what is proven while a claim that says "the protocol"
overstates it. In every crate below, "complete" and "every function" mean the
protocol functions: the persistence codecs (`from_bytes`, `to_bytes`, their
entry decoders and length helpers) and a few accessors are translated and
carry no theorem, as CLAIMS.md's "Translated is not proved" lists.

One exception, added by `Translation/ImportInv.lean` and worth stating
precisely because it is narrow. In `tacenta-ratchet`, `tacenta-spqr` and
`tacenta-braid`, `from_bytes` now carries a **constructor** theorem: a state it
returns satisfies that crate's own `invariant()` (for the first two, every
clause of it; for the Braid, the clause `ct1_bounded`, and in the complete session unit
also `decoders_bounded`), and the
invariant yields as many of the T1 and T3 preconditions as it reaches. That is not a T1 theorem -- it says nothing about
whether `from_bytes` can panic, only what is true of a state when it does
return one -- and it is about the *leaf crate's* persistence format. The
session layer that calls these codecs, in `tacenta-core/lifecycle/src`, is
translated and has conditional panic-freedom theorems for its entry points, all
conditional on records that are inhabited only in the sense of "The four contract records follow from an axiom base that has a model, under five laws" (three of them on a record that had a false field until it was
restated; `GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`), but
none for import or export, so nothing here says what a session restored
from disk satisfies.
`to_bytes`, the entry decoders and the length helpers still have no theorem of
any kind, as do the codecs of the other four crates, with two exceptions:
`Translation/RatchetCodecT1.lean` and `Translation/SpqrCodecT1.lean` prove
`tacenta-ratchet`'s and `tacenta-spqr`'s `from_bytes` and `to_bytes`
panic-free, each decoder under a slice-length precondition every Rust slice
meets and each encoder under its crate's `ZeroizingVecTotal`.
`Translation/ErasureCodecT1.lean` does the same for `tacenta-erasure`'s
`Encoder` and `Decoder` codecs -- the erasure crate's own translation; in the
Braid's translation these functions are opaque declarations the proof does not
reach -- with the decoder also under `DivCeilTotal`.

**How far it reaches, in one line: a decoded state is panic-free
unconditionally; it refines the model provided the relevant counter has a step
of headroom left.** The reason is the same in all three crates and is not a
weakness of the proofs. Each crate reserves the top value of the counter it
steps -- the classical ratchet's clock clamps at `MAX_EVENTS = u32::MAX - 1`,
the sparse ratchet's `advance` refuses the step to `epoch == u64::MAX`, the
Braid's `step_receive` refuses the same in transitions (5) and (13), as
`tacenta-spec/protocol/mlkem-braid.md` numbers them in "The state machine" --
so that no state a crate's operations produce is one its own decoder refuses.
The three models used to reserve nothing, and no longer do: they stop at the
ceilings the pages state and the crates keep (`Model.State.maxEvents`, and the
`ns` and `nr` refusals at `u32::MAX`; `Model.SparseRatchet.u64Max`, reserved as
an epoch and refused past as a chain's counter; `Model.Braid.u64Max`, the epoch
transitions (5) and (13) refuse to step onto). The persistence vectors pin the
two ratchets' ceilings. No vector pins the Braid's, because no vector file
holds a Braid state: its crate tests it, and `Model.Braid.receive_epoch_lt`,
`receive_advance_lt` and `receive_output_epoch_lt` state it of the model. The
refinement theorems still ask for the step of headroom they asked for when the
models did not stop (`events + 1 < u32::MAX`, `epoch + 1 < u64::MAX`): for the
classical clock the agreement no longer needs it, and for the sparse epoch
`advance_refines` reads the model's refusal as the mismatch refusal, while the
top-level refinements may not need it. For the Braid, code and model both
answer `Failed` at `epoch = u64::MAX - 1`, and the proofs use `hepoch` to rule
that arm out rather than relate it; whether it is needed has not been checked. Dropping those premises is a
restatement of the theorems not yet made. No
`invariant()` can supply the step, because the state at the last unreserved value is an ordinary state
the crate produces, decodes and goes on operating on. The headroom is
therefore the caller's premise wherever a refinement is composed with a
decoded state: an explicit argument on `Ratchet.decoded_receive_refines`, and
an open premise for the other two, which have no refinement corollary. The
panic-freedom corollaries take no such premise at all.

Two further things that constructor theorem is not. It is **not** a preservation
theorem: no theorem in this tree says that `send` or `receive` carries a state
satisfying a crate's `invariant()` to one that still does, so satisfying the
predicate is not by itself evidence that a run of the crate could have
produced the state. Whether the decoder's refusal is a consistency check
rather than a policy turns on exactly that -- on no run producing a state the
predicate rejects -- and that is a property the crates establish in the Rust,
beside the counters concerned and in their import tests, not one this tree
proves. CLAIMS.md says the same where the theorems are listed.

And, until recently, it was **not** known to be non-vacuous. "If `from_bytes`
returns a state, that state satisfies `Inv`" is true of a decoder that refuses
every buffer, so the theorem needs a witness the way the boundary hypotheses
in `Translation/Satisfiability.lean` do.
`Ratchet.from_bytes_establishes_inv_nonvacuous` supplies one for
`tacenta-ratchet`: a concrete 185-byte string the *translated* `from_bytes`
accepts, kernel-checked (`decide` on a list literal, no `native_decide`) and
pinned. The sparse ratchet and the Braid have witnesses for the leaf translation in modules of their
own: `SpqrFromBytesWitness.lean` proves a 140-byte string accepted by the sparse
ratchet's `from_bytes` (version 1, an all-zero root key, epoch 0, one chains entry at epoch 0 with
both chains absent, no skipped keys), with a state that satisfies `Spqr.Inv`, and
`BraidFromBytesWitness.lean` (and, for the complete Session unit,
`SessionUnitBraidFromBytesWitness.lean`) a 74-byte string accepted by the Braid's
(version 1, state tag 0, epoch 1, a zero authenticator), with a state that satisfies
`Braid.Inv` under the one hypothesis `from_bytes_establishes_inv` already takes. `Braid.Inv` has one
clause, a ciphertext-length bound that is `True` outside tags 3, 4, 7, 8 and 9, so on that state it is
trivial: the result shows that the decoder accepts a string and that the premise of
`from_bytes_establishes_inv` is satisfiable, and it does not exercise the clause. The session unit's sparse
decoder has no witness. No opaque constant is called on either decode path, so acceptance itself needs no
assumption; the Braid pins list `tacenta_erasure.*` and `tacenta_kem.*` constants only because those names
occur in the definitions of the decoder's other arms and of `Braid.invariant`, which the statement
mentions.
**What is still not shown** is acceptance of a Braid state that holds an erasure or KEM
value (tags 1 to 10): their decode runs through the opaque erasure and KEM decoders, which
no byte string can be shown to satisfy from inside the translation. For those states
the only evidence that the decoder accepts anything is the Rust round-trip tests.

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
  `tacenta-core/lifecycle/src/lifecycle.rs`, which is translated but neither
  modelled nor proved, so a swap there would pass every proof, every vector and
  `attest`. The pairing is tested, not proved:
  `a_session_dh_step_pairs_the_old_key_with_the_peers_new_key`
  (`tacenta-core/tests/handshake_to_ratchet.rs`) runs a real `Session` through
  a step and checks that a message sent under the peer's new key decrypts,
  which it does only if the receiving chain was seeded from the old key pair
  with that key, and that the sending public key changes at the step. It
  checks the session by running it, not against a model scenario.
- `tacenta-core/session` (`tacenta-session`): the PQXDH derivation. T1, T2, T3.
- `tacenta-core/erasure` (`tacenta-erasure`): Reed-Solomon over GF(2^16).
  Translates with no gap, and **T1 complete for the coding functions**: the
  field arithmetic, interpolation, the chunk helpers, and both public entry
  points of each of the encoder and the decoder are proved panic-free. Not
  `Encoder::new`, `Decoder::new`, `needed`, `received`, `encoded_len`,
  `to_bytes` or `from_bytes`, which have no theorem; `Decoder::from_bytes` refuses by
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

  The refinement rests on the kernel's three axioms alone.
  `#print axioms Tacenta.ErasureT3.mul_refines` is pinned under `#guard_msgs` in
  `Translation/ErasureT3.lean`, so a compiler-trust axiom cannot appear
  unnoticed. Until 2026-10-01 it rested on one `bv_decide` reflection, in
  `clmulUpto_sixteen`.

  Worth naming because this is the crate where the claim is worth most and was
  cheapest to get. A decoder consumes codewords an attacker supplies, and every
  index and length in it is computed from what they sent. The crate has no
  dependencies, so most of its theorems carry no boundary assumption at all:
  `next_chunk_no_panic` rests on `propext`, `Classical.choice` and `Quot.sound`
  and nothing else, where the ratchet's carry three.

  Two assumptions in the file, and the axiom lists say which theorems carry
  them. `usize::div_ceil` and `Vec::truncate` are both functions the translation
  does not model, so they arrive as axioms and nothing can be said about them,
  including that they return. `DivCeilTotal` is stated under `b.val ≠ 0`,
  the one input on which `usize::div_ceil` panics being a zero divisor, and
  its one use divides by the constant `CHUNK_BYTES`. Both are the toolchain
  not seeing through a core library function rather than a primitive we
  chose to trust, and neither guards a secret.

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

  **The verified protobuf reader has no caller.** Outside its own directory
  `tacenta-protobuf` is referenced only by the `protobuf_bodies` fuzz target.
  The decoders a peer's bytes actually reach are `decode_message` and
  `decode_composite`, for a ratchet message, and `decode_initial`, for a
  prekey message; a fetched prekey bundle goes through `decode_bundle`. All
  four live in the `tacenta-wire` leaf crate, which the root crate's
  `serialization` module re-exports, and they are translated and proved:
  `Translation/WireT1.lean` shows they cannot fail on any byte string,
  `Translation/WireT3.lean` that `decode_composite` returns exactly what
  `Model.CompositeHeader.decode` returns, `Translation/WireInitialT3.lean`
  that `decode_initial` returns exactly what `Model.Messages.decodeInitial`
  returns, and `Translation/WireBundleT3.lean` that `decode_bundle` returns
  exactly what `Model.Messages.decodeBundle` returns, all kernel-only. So for
  both kinds of message and for a bundle, what is parsed out of the bytes it
  arrived as is proved to be what the model parses; what the session then
  does with the parsed message is not translated, and the
  protobuf crate's T1 and T3 remain a verified reader the product does not use.

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
- **No `Vec::pop` analogue.** `Vec::extend_from_slice` is modelled by the
  Aeneas library rather than left an axiom, so this zone adds no `Vec` boundary of the ratchet's kind
  (`Vec::pop`, `LawPop`). It does declare the `Vec` `Zeroize` implementation, which
  `SessionT1.shared_secret_no_panic` and `SessionT3.shared_secret_refines_some` carry in their pins.
- **The two constant comparisons are kernel proofs**: that the domain
  separator and the parameter label written as Rust byte strings are the ones
  the model writes as lists of code points (`fPrefix_agrees`, `skInfo_agrees`). Until 2026-10-21 they were
  decided by `native_decide` and the pin in `Translation/SessionT3.lean` listed one compiler-trust axiom for each;
  they are proved by `simp` and `rfl` now, and the pin lists none.

### The three-leaf translation unit is an eighth zone, and it ships to nobody

`tacenta-core/triple-unit` is a verified zone in `attest.py` and a crate in the
workspace, and no shipping path reaches it. No shipping crate depends on it, it
exports nothing anyone calls, and deleting it would change no behaviour that
anybody observes. It exists to be translated and proved about, and proofs do
depend on it: every `Translation/Unit*.lean` file is a statement about its constants, and the
Triple Ratchet's T1 and T3 are proved nowhere else.

**What it is for.** Translating `tacenta-core/triple` on its own gives Aeneas
three crates and lets it see one. The Double Ratchet's and the sparse ratchet's
operations arrive as opaque externals -- thirty-five axioms -- so the Triple's
T1 on that translation had to assume exactly what the leaves' own T1 proves, and
its T3 joined the two halves by hand in bundle clauses a script compared against
the leaf theorems. That comparison was a check on a hand-written link, not a
proof that there is no link to write. The unit removes the need for one, and the
standalone translation and those proofs were deleted after 2a89a7f:
it presents the three leaves to Aeneas as three modules of one crate, so the
leaf operations translate to definitions and the Triple's bodies call them
directly. The thirty-five axioms go, and the unit declares nineteen, exactly
the union of what the two leaves declare on their own.

**The gap it leaves, which is the point of listing it here.** The unit is the
same text and not the same crate graph. Two of its three modules are the leaf
files themselves, loaded with `#[path]` rather than copied; the third is the
Triple's `lib.rs` byte for byte plus a generated header and one `use` that
brings the two sibling module names into scope, since a path's first segment
resolves in the current module and the extern prelude and not in the parent.
It is a workspace member, so it compiles under the same profiles, the same
lockfile, the same edition and the same `overflow-checks`. What differs is the
crate boundary: in the shipping build these are three crates, and here they are
one. Name resolution, monomorphisation and the borrow check all run after the
module structure is fixed, and each leaf's `#![forbid(unsafe_code)]` still
bounds its own module, so we do not know of a way the difference changes a
function body. "We do not know of a way" is the claim, and it is weaker than a
proof. A reader who holds that what is proved must be what ships should count
this boundary as a gap, and this paragraph is the disclosure of it.

**What holds the unit to the leaves.** `assemble-triple-unit.sh --check`
regenerates the whole tree and diffs it against the committed one, so a hand
edit anywhere in the unit fails. Within that, the copied file is read back:
the inserted block is found by its text and deleted, the remainder must be the
leaf exactly, and no top-level inner attribute may follow the inserted `use`.
`attest.py --check` records the assembly script's hash and the hashes of all
three leaf trees, which is what catches a leaf moving under a unit nobody
re-assembled -- the case where the unit's translation goes stale while the unit
crate in the tree still looks untouched. An earlier version of the byte-identity
check stripped the same line ranges it had written and so could not fail; it
was replaced after an external review, and the replacement was tested by
forcing the misread it claims to catch.

**What is proved about it, and what is not.** The unit is translated with no
`sorry` and no body Aeneas gave up on. The two leaf panic-freedom proofs have
been restated about it, as `Translation/UnitT1.lean` and
`Translation/UnitSpqrT1.lean`, so the Double Ratchet and the sparse ratchet are
proved panic-free as compiled inside the unit and not only as compiled alone.
Those files are generated from the leaf proofs by
`scripts/port-unit-proofs.sh`, which rewrites the import, the namespace and the
`open` and copies every proof body unchanged; `--check` regenerates and diffs
in CI. `Translation/UnitPins.lean` pins each theorem's axiom base and holds it
to the leaf's, name for name, so the port cannot quietly add an assumption,
turn an assumption into a definition, or make a kernel-only proof
compiler-trusted.

The port is not a re-import and could not have been. The leaves' proofs are
stated about the leaves' own translated constants, which are different
constants; nothing connects them, so the theorems exist twice. Generating the
second copy is what keeps that duplication from becoming drift. For the same
reason the unit's translation cannot be imported into the same Lean environment
as the leaves' -- the instances collide -- which is why it has an axiom audit
module of its own, `Translation/AxiomAuditTripleUnit.lean`, and why the two
worlds stay separate.

**The Triple's own T1 and T3 are proved on the unit, and they replaced the
standalone proofs.** `Translation/UnitTripleT1.lean` **proves** all seventeen of
the `*Total` bundles the standalone `TripleT1.lean` assumed, from the two leaf
theorems above, and `Translation/UnitTripleT3.lean` proves the two refinement
bundles the standalone `TripleT3.lean` assumed. That is what the unit exists
for. The standalone translation, those two files, their satisfiability
witnesses, their axiom audit module and the script that compared the refinement
bundles with the leaf theorems by text were deleted after 2a89a7f.

**The Triple's unit proofs are hand-written, unlike the leaves' copies.**
`Translation/UnitT1.lean` and `Translation/UnitSpqrT1.lean` are generated and
diffed in CI, so an edit to a leaf that is not carried across fails the build.
`UnitTripleT1.lean` and `UnitTripleT3.lean` could not be generated: they began
as `TripleT1.lean` and `TripleT3.lean`, which wrote translated names in qualified
form (forty-nine in `TripleT1.lean`), and their proof bodies genuinely changed
(roughly twenty newly-in-scope `@[step]` rules meant pruning rather than
substitution, and several boundary assumptions collapsed into the leaves'). With
the originals deleted there is nothing for them to drift from; they are ordinary
hand-written proofs.

**Four preconditions land outside the translated tree.** Proving the bundles
instead of assuming them means carrying the leaves' real preconditions, which
the standalone proof's unconditional bundles hid: `State.send` on the unit needs
`self.post_quantum.chains.length + 1 < Usize.max`, and `State.receive` needs
`max self.classical.skipped.val.length MAX_SKIPPED_STORE.val + MAX_SKIP.val ≤ Usize.max`,
`self.post_quantum.chains.length + 2 < Usize.max` and
`self.post_quantum.skipped.length + MAX_SKIP.val ≤ Usize.max`. Nothing on the
unit island discharges them. They are obligations on the **unproved session
layer** in `tacenta-core/lifecycle/src`, which decides how large a skipped-key
store and a chain table a session may carry. That layer is translated in the
Phase 0 lifecycle module but is not proved in its own right. The classical one is discharged in the other
island, by `Ratchet.inv_gives_store_bound` in `Translation/ImportInv.lean` and
through it by `Ratchet.decoded_receive_no_panic`, for a state that came from
`from_bytes`; "Eight theorem-bearing zones on the shipping path" above describes that
route. It has not been ported to the unit, so it does not reach these
theorems. All four hold of any state that could exist, at either platform
width. They are bounds against `usize::MAX` on quantities a real session keeps
in the low thousands.

**The satisfiability guard is narrower than it reads, and the gap is where
this tree's worst defect lived.** `Translation/Satisfiability.lean` and
`Translation/UnitSatisfiabilityTriple.lean` exhibit a witness for a boundary
assumption, and for several also prove that the over-broad version of the same
assumption admits no implementation at all. That is a real guard against
assuming something nothing could satisfy. What it covers is the *opaque
operation* family: the `Vec` operations, the `zeroize` wrapper and its models,
the key-derivation agreements and totalities, `Option`'s clone, and the erasure
crate's `div_ceil` and `truncate` -- some of the totalities only by derivation
from a witnessed agreement.

It does not cover the **numeric preconditions**, the store, chain-length and
counter bounds a `no_panic` or `refines` theorem carries about a state's sizes.
That is the family the defect corrected on 2026-09-10 lived in: `receive`'s
store bound asked for something no state with anything in it could satisfy at
32 bits, and sat in this file for months described as a genuine constraint.

Two things now bear on that family, and they should not be mistaken for more.

**A lint trips on some textual forms of the class the defect belonged to.**
`tooling/check-precondition-shapes.py` refuses a bound comparing an additive
term that is one integer type's maximum `A` with a bound that is another's
maximum `B`, where `A` is at least `B` on some target, because there the bound
forces what it constrains to zero. It recognises six comparison forms and a
fixed list of ways to write a maximum, one declaration at a time, and reports
each site at the line and column of the offending maximum. Its docstring lists
exactly which forms and spellings it catches, which ones review has found it
misses, and which legitimate code it refuses. Those lists are the claim, and
nothing here extends it.

Getting that claim true took four rounds, and the failures are worth recording,
because each one was a guard described as more than it was. The first version
accepted a flipped comparison, a parenthesised addend and fully qualified names.
The second reported several sites in one declaration as a single site. The third
reported every site at the maximum after the one at fault, could be slipped past
by any declaration its detector did not recognise, and still accepted three
spellings of a maximum this tree uses elsewhere. Every one of those is now a
fixture case. The fourth round's fixes were each confirmed by breaking them and
watching their cases fail.

Run against the tree as it stood before the fix, it reports **twenty-one**
sites in sixteen declarations across six files: fourteen hypotheses, one
conclusion, two assumption-bundle definitions, and four restatements of the
bound inside one proof. Three of the sixteen declarations are in
`ImportInv.lean`, which took the platform fact as an argument. That matches a
reviewer's independent count file for file, and each of the twenty-one reported
columns lands on the offending maximum.

**The class is proved to be the right thing to refuse.**
`Translation/PreconditionShapes.lean` refutes both forms the defect took: the
store bound admits no store at 32 bits, and the skip bound admits only the
empty one. That file is excluded from the lint, because it states the shape on
purpose. The lint checks only that both refutations are still present by name.
It does not check what they say, and it scans nothing else in that file. An
earlier version tried to excuse the refutations by name and binder instead, and
review found five ways to smuggle an ordinary precondition past that.

An earlier version of that file claimed to witness the numeric preconditions
through "six shapes"; a cold read showed the six covered under half of the
theorems, and that the witnesses were connected to none of them, since nothing
compared a witness with any theorem's hypothesis. Those witnesses were removed
rather than defended. The tree now holds replacement evidence, and it is
narrower than the claim that was removed:

- For the receive and send theorems of the classical ratchet, the sparse
  ratchet, the Triple Ratchet and the Braid (44 theorems, on the standalone
  translations, the three-leaf unit and the session unit),
  `Translation/NumericWitnessLeaf.lean`, `NumericWitnessTriple.lean` and
  `NumericWitnessSession.lean` prove that the theorem's numeric premises, its
  numeric predicates about a state and its relations between a translated and a
  model value hold together at a concrete state, at both platform widths.
  `scripts/check-precondition-witnesses.sh` reads each theorem's type from the
  built environment and refuses the module if its statement is not the
  theorem's own premises, if a premise of the theorem is left unclassified, or if
  the witness proves anything else. A premise added to one of these theorems is
  therefore refused until someone classifies it. For the three discharge-only
  theorems (`advance_refines`, `maybe_advance_refines`, `clear_old_epochs_refines`)
  classifying it is all that is asked: a numeric premise tabled as `caller` needs
  no witness. The script recognises a numeric premise by a comparison or by the
  name of a numeric state predicate, so one hidden behind another definition and
  tabled `boundary` is accepted, and it does not tie the state a witness proof uses
  to the state the decoder-invariant theorems are about. That is the join the
  removed witnesses lacked, for these theorems only.
- `Translation/NumericBoundary.lean` proves the bounds against the code's caps
  at both widths (the 32-bit erasure room bound is exactly
  `needed ≤ 2^27 - 1`) and that the two ceilings the invariant leaves open on the
  clock and the epoch, `events + 1 < u32::MAX` and `epoch + 1 < u64::MAX`, each
  exclude exactly one value among those the decoder's invariant allows; `hnewb` and
  `hcounter` have no such theorem. `NumericShapeWitness.lean` shows each of 61
  shapes of numeric premise, as enumerated once, satisfiable at both widths. The
  enumeration is not complete (the codec theorems' `pos + 41 ≤ usize::MAX` and
  `len + 48 ≤ usize::MAX` have no shape) and nothing in the tree checks it. Those
  theorems are about shapes and are joined to no theorem; their statements are
  held by `#guard_msgs in #check` pins in the build; `attest.py` requires each pin
  to exist (`REQUIRED_STATEMENT_PINS`) and reads what it says only to refuse a cut-off `⋯`.
- The store bounds the classical ratchet's `receive` carries are satisfied by
  every state its decoder accepts (`Ratchet.inv_gives_store_bound`,
  `Ratchet.store_plus_skip_fits`), and the sparse ratchet's room bounds likewise
  (`Spqr.inv_gives_chain_room`, `Spqr.inv_gives_skip_room`), which is far
  stronger than a witness. `Translation/DecodedStateDischarge.lean` adds that the
  `epochsKept` family on the sparse ratchet's refinement (`hcb`, `hsb`) follows
  from the invariant and `hepoch`, and the session unit's copy adds the Triple's
  composed refinements.

What is **not** established. The helper theorems of the T1 and T3 files, the codec
and parser theorems and the dispatch layer have no witness in the tree; their
numeric hypotheses are discharged inside the proofs that apply them, which is read
and not checked. The
Braid's relations between a translated and a model Braid, the arms of
`ct1_bounded` and `decoders_bounded` that hold a KEM value, and the premise that
a byte string decodes to a given state have no witness (they need values of opaque
types), and the lifecycle headroom records have none either. Nothing was built or
run at 32 bits: `Usize.max` is an opaque constant of which only its two values are
known, so each proof covers both widths by being about the constant. The values
of the constants in the translations are evaluated by `NumericBoundary*.lean`, and
the ratchet's and the sparse ratchet's agree with the model's; that they equal the
Rust source's rests on the translation attestation. A one-off script run over the
built environment, on the theorems that have numeric hypotheses, found none of
those hypotheses false or unsatisfiable at either width. It did not enter every
comparison (those under `match`, `or`, `not` and `!=`), and it covered the helper
theorems and the dispatch layer by script alone. The script is not in this tree,
so it is not evidence the tree can repeat.

**Satisfiable is not satisfied by every state.** A witness says a hypothesis is
not vacuous. It does not say every reachable state meets it. The clock headroom
on the refinement of `receive` is satisfiable and excludes the parked clock, an
ordinary state a session reaches, and `PreconditionShapes.lean` states both
facts beside each other (`NumericBoundaryLeaf.clock_ceiling_summary` adds that the
parked clock is the only value the decoder's invariant allows that fails it). The
epoch step on the sparse ratchet's refinement is another instance.

The unit island has witnesses of the first kind and none of the second.
`UnitSatisfiabilityTriple.lean` witnesses every boundary hypothesis the Triple's
discharged refinement takes, `UnitT1.DerivedKeysModel`,
`UnitSpqrT1.OptionCloneTotal` and the HMAC and HKDF agreements among them; the
passage on the Triple's refinement below lists them. The leaf island's copies of
those hypotheses are witnessed in `Satisfiability.lean`, the shared-wrapper ones
jointly. Three of `UnitTripleT1.lean`'s totality
hypotheses have no witness of their own but follow from witnessed ones.
`KdfRkTotal` and `KdfCkTotal` are *derived* in `UnitSpqrT3.lean` from
`SpqrHkdfAgrees` and the `zeroize` round trips, and `KdfInitTotal`, which has no
leaf twin, is what `UnitSpqrT3.kdf_init_refines` gives under the same
hypotheses, though no theorem states that step. Whether each of
`UnitTripleT1.lean`'s other hypotheses follows from a witnessed one has not been
checked hypothesis by hypothesis.

Transporting them to `self` is free only because the clone is provably the
identity on the unit -- every field is an array, a scalar, an `Option` under
`OptionCloneTotal`, or a `Vec` whose elements clone as the identity.
The standalone `TripleT1.State.clone_no_panic` proved only that the clone
returns, which was all it could prove where the inner states were opaque, so
there a precondition could not be transported at all.

**And the composed `receive` takes on boundary axioms.**
The standalone `Tacenta.TripleT1.State.receive_no_panic` depended on twelve
axioms, none of them compiler-trusted, measured before its deletion. The ported
theorem depended on seventeen when it was ported and depends on fifteen since the
KDF change (ADR-0010) made the KDF's two axioms translated definitions: the three
standard axioms and twelve boundary axioms of `zeroize`, `Vec` and `Option`,
none of them compiler-trusted and none of them the KDF's. The difference is not
a weaker proof: the standalone theorem had fewer axioms because it *assumed* the
sparse ratchet's receive is total rather than proving it. The ported one proves
that part and inherits the boundary axioms proving it needs. The three extra axioms
(five before the KDF change) are a substitution rather than a new kind of trust --
the bare operation axioms are replaced by `zeroize`, `Vec` and `Option` boundary
axioms already shared with every other proof in the tree (and, before the KDF
change, by the KDF's `hmac_sha256` too). `Translation/UnitPins.lean`
records the whole base and `CLAIMS.md` repeats it.

**The refinement layer is on the unit too, with its trust base unchanged.**
`Translation/UnitT3.lean` and `Translation/UnitSpqrT3.lean` are `T3.lean` and
`SpqrT3.lean` generated onto the unit by `scripts/port-unit-proofs.sh`, so the
classical and sparse ratchets are proved to refine their models as compiled
inside the unit, and not only as compiled alone. Measured on 2026-09-10, every
one of the 115 public theorems in the two copies depends on exactly the axioms
its leaf twin depends on, once each translation's crate prefix is set aside.
The same eight compiler-trust axioms appeared on both sides then (none since 2026-10-21, when the sparse ratchet's
constants became kernel proofs), and 61 of the 115 were kernel-only on both. Outside the 115 there is one difference, and it runs
the other way: the matcher Lean generates for `maybe_advance_refines` and its
two congruence equations depend on `propext`, `Classical.choice` and
`Quot.sound` in `SpqrT3.lean` and on no axioms at all in `UnitSpqrT3.lean`. It
is already there in the matcher, before any proof uses it. That comparison was
run once, by a probe outside the tree. The pins in `UnitPins.lean` enforce it only for the three theorems
`T3.lean` pins, so a later change could move the rest without failing a build.

Neither copy is a pure copy. In both, qualified references to the leaf proofs'
namespaces are renamed, inside statements and proof bodies as well as prose,
and the sparse copy carries one inserted erasure. On the unit the two ratchets
share one set of `zeroize` constants, so `UnitT1.zeroizing_deref_step`, a
stepping rule `UnitT1.lean` registers for the classical ratchet, reaches a goal
in `UnitSpqrT3.lean` that it cannot reach in the leaf island. One proof stopped
short there, demanding `UnitT1.ZeroizingTotal`, which nothing in that file
provides. The generator inserts an `attribute [-step]` line removing that rule;
no statement and no proof body changes. Two more `UnitT1.lean` rules sit on
constants the unit shares, and removing them as well changes no proof term, so
they stay. The removal is scoped to the copy: a module that imports
`UnitSpqrT3.lean` has the rule back, so the Triple's refinement, once it is on
the unit, needs its own.

This is the first place a leaf stepping rule reached a goal in a copied proof
that it could not reach before, and it need not be the last. It is not the
first effect of the shared constants on the copies, though. The sparse copies'
proof terms already name different auxiliary constants from their leaves': where
`SpqrT1.receive_no_panic` uses its own crate's `State.receive.match_1`,
`UnitSpqrT1.receive_no_panic` uses
`tacenta_triple_unit.tacenta_ratchet.State.started_as_sender.match_1`, a matcher
from the classical crate that Lean reuses because it is the same term.

**The Triple's refinement is on the unit, with both bundles proved.**
`Translation/UnitTripleT3.lean` proves the Triple's refinement on the unit, and
`Translation/UnitSatisfiabilityTriple.lean` holds the Triple's two satisfiability witnesses
and witnesses the inner boundary its discharged theorems take. On the unit, the hand-written bundles the standalone `TripleT3.lean` had to assume,
`RatchetAgreesFor` and `SpqrAgreesFor`, are proved. The inner states are
concrete, each inner refinement relation fixes every field of its model state so
the abstraction can be written down, and every clause follows from a unit theorem
(`ratchet_agrees_for`, `spqr_agrees_for`). `send_refines_discharged` and
`receive_refines_discharged` state the composed `send` and `receive` with both
bundles discharged. What that does and does not buy:

* **Most of the trust-base change is the unit translation's, not the
  discharge's.** Measured on 2026-09-10 with `#print axioms`:
  the standalone `TripleT3.send_refines` rested on sixteen opaque declarations of the inner
  crates, the two state types and fourteen calls. On the unit those calls are
  defined, so `UnitTripleT3.send_refines`, with the bundles still as hypotheses,
  already rests on none of them, and on the external primitives the inner
  refinements rest on instead (HMAC, the `zeroize` wrapper and trait, `Vec::pop`,
  `Vec::capacity` and `Vec::zeroize`, `Option`'s clone), with the same one `native_decide` axiom (the Triple's combine
  label's). Discharging the bundles added exactly the eight `native_decide` axioms
  `UnitSpqrT3.lean` carried, and nothing else, so the discharged theorems listed nine; the same held for `receive`.
  Since 2026-10-21 all nine are kernel proofs, and none of the four theorems, undischarged or discharged, lists a
  compiler-trust axiom.
  `UnitPins.lean` pins all four new theorems.
* **There are more hypotheses, not fewer**, because the standalone theorems hid
  the inner boundary inside the bundles, as the standalone file's header said. One
  HKDF agreement serves all three crates, and the general `ZeroizeTotal` gives the
  Triple's narrow one, so neither is listed twice. Proving the classical `clone`
  clause needs `OptionCloneTotal`. Each bundle covers its ratchet's whole calling
  surface, so the `send` theorem assumes the receive path's boundary as well.
* **The boundary hypotheses of the discharged theorems about opaque constants are
  witnessed on the unit, and the six about translated functions follow from laws or are proved.**
  `UnitSatisfiabilityTriple.lean` witnesses those about the unit's opaque
  constants. Its witnesses of the HMAC and HKDF agreements (from the model's output lengths) are void bridges
  since the KDF change (ADR-0010), the KDF being a translated definition in the unit, and `KdfTripleUnitAgreements` proves
  `UnitT3.HmacAgrees` and `UnitT3.HkdfAgrees` instead. Where two constrain one constant it witnesses them jointly: the
  classical round trip, which is also the Triple's, the sparse round trips at 96
  and 64 bytes and `DerivedKeysModel` all constrain one `zeroize.Zeroizing`
  family. The four other ones about translated functions, `UnitT1.RemoveSkippedAtTotal`,
  `UnitSpqrT3.RemoveSkippedAtAgrees`, `UnitSpqrT3.VecRetainAgrees` and `UnitSpqrT1.VecRetainTotal`, have a void bridge or no
  witness there, and `UnitSatisfiabilityTripleLaws.lean` proves each from named laws
  (`CLAIMS.md`).
  The rest each constrain a constant nothing else mentions, and that their
  separate witnesses combine is an argument in prose, not a checked one. Two
  `example`s apply the discharged theorems to exactly the witnessed hypotheses,
  so one added ahead of the state relation stops the build; nothing checks the
  preconditions after it. The leaves' copies are witnessed the same way in
  `Satisfiability.lean`, jointly where one leaf theorem takes two hypotheses about
  one wrapper (`T3.lean` takes both `ZeroizingRoundTrips` and `T1.DerivedKeysModel`,
  and the sparse ratchet's refinements both of its round trips), though nothing
  there checks the list against the leaf theorems' signatures.
* **The port is hand-written.** It began as `TripleT3.lean` and differs from it in
  more than names; its header lists each difference against that file as of
  2a89a7f. Three stepping-rule erasures keep the
  original proofs elaborating: one retargeted from the original, and two for rules
  `UnitTripleT1.lean` registers that `TripleT1.lean` never did.
* **The standalone proofs are gone.** `TacentaTriple.lean`, `TripleT1.lean`,
  `TripleT3.lean`, `SatisfiabilityTriple.lean`, `AxiomAuditTriple.lean` and the
  bundle drift checker were deleted after 2a89a7f. The comparisons above with
  `TripleT3.send_refines` were measured before that.

**The eleven waived compiler-trust axioms are here.** Putting all three leaves'
types in one module makes eight string literals occur more than once across
their `Debug` bodies, and `decide +native` caches by statement, so eleven of the
axioms it names are left declared and reached by nothing. The axiom audit
waives its "the parent applies it" requirement for them; "The proofs are
trusted by evaluation, not only by the kernel" above states the waiver and its
bound.


### The Braid-and-erasure translation unit is a ninth zone, translated and not yet proved about

`tacenta-core/braid-unit` is the ML-KEM Braid and its erasure codec compiled as
one crate, assembled by `scripts/assemble-braid-unit.sh` the way the three-leaf
unit is: the erasure leaf loaded with `#[path]`, the Braid's `lib.rs` copied
with one inserted `use crate::tacenta_erasure;`, and the unit held to its
leaves by `--check` and by `attest.py`. What the section above says about the
crate boundary as a gap applies to it unchanged, and it ships to nobody.

**What it is for.** In the Braid's own translation the erasure codec's types
and operations are twenty-three opaque axioms, and the Braid's proofs assume
them: seven totality assumptions in `BraidT1.lean`, and `ErasureAgrees` and
`ErasureCloneAgrees` in `BraidT3.lean`. In the unit they are definitions. Its
translation declares no erasure axiom; in their place are two library
functions the codec's bodies reach, `Vec::truncate` and `usize::div_ceil`, which
the erasure crate's own translation declares too. The KEM stays opaque, since
it is a trusted primitive zone rather than a verified one.

**What is proved about it: nothing yet.** The unit is translated with no
`sorry`, and `Translation/AxiomAuditBraidUnit.lean` audits its axioms, but no
theorem is stated about its constants. The Braid's T1 and T3 are still the
standalone ones, over the opaque codec, and every assumption named above is
still an assumption. Porting those proofs to the unit, so that the erasure
crate's own theorems discharge them, is what the unit is for and has not been
done.

### The lifecycle leaf is a tenth translated zone, with no theorem on its own island

`tacenta-core/lifecycle` is the shipping session orchestration behind the
`tacenta_core::sessions` API, which since identity records offers the initiator's
establishment only through a wrapper outside this leaf (the next section). Charon starts from every public item,
and `TacentaLifecycle.lean` contains all 30 public lifecycle operations and
their reachable call graph. The coverage gate compares the Rust surface with
the generated definitions, and its missing-root control proves that omission
turns the gate red.

This is a Phase 0 translatability result. No T1 or T3 theorem is stated about
the standalone `TacentaLifecycle` constants (the theorems about the lifecycle
live on the eight-leaf session unit, next section), and the leaf translation sees the ratchets, Braid,
wire layer and primitive boundary as 113 opaque externals. The manifest lists
all 113 and `AxiomAuditLifecycle.lean` checks the elaborated module against
that exact set. Of the 113, 53 are first-party leaf operations the lifecycle
calls across a crate boundary (`tacenta_session`, `tacenta_wire`,
`tacenta_triple::State`, `tacenta_braid::Braid`, `tacenta_ratchet`,
`tacenta_spqr`; until the KDF change (ADR-0010) also `tacenta_kdf`'s HMAC, translated since): each has a body and, for most, a theorem in
its own translation, but on this island they are bare axioms with no
precondition, exactly the standalone-Triple shape the three-leaf unit was
built to remove. Twenty-two are `tacenta_boundary` declarations, the primitive
boundary this carve-out created: three key types and nineteen operations
over X25519, the identity-key predicate, the AEAD, ML-KEM-1024 and XEdDSA,
whose bodies are trusted and
never translated ("Trusted, not verified" above now lists the crate). The
rest are standard-library, `zeroize` and `rand_core` items. Randomness
reaches the lifecycle as a `rand_core::RngCore` trait dictionary rather than
a boundary function, which is why no `random32` declaration exists and why
`tooling/check-lifecycle-boundary-surface.py`, which follows only
`tacenta_boundary` names, cannot see that route.
`tacenta-model/SESSION-L4-PHASE0-SPIKE-20260918.md` maps the reachable
boundary declarations to the contracts the primitive-boundary decision
names (ten in the record, twelve after its first dated note, thirteen after the second, fourteen after the third). Later phases assemble the lifecycle with its eight code leaves
and prove orchestration against the lifecycle model; until then,
`Session::encrypt`, `Session::decrypt`, establishment and persistence remain
tested and translated, not proved end to end.

### Identity records, and the initiator's public entry, are outside the translated zone

`tacenta-core/src/sessions/identity.rs` holds the identity pair digest, the
verification number, the classification of a key against a record, the lookup
across records, initiator establishment under an expectation
(`establish_initiator`) and the responder's `establish_responder_unattributed`
(ADR-0009; REQ-AUTH-02, -15 and -16). It is in the `tacenta-core` crate itself,
not in a leaf crate, and nothing translates it: no T1 or T3 theorem, on any
island or unit, is about any function in it.

- **What exists.** Tests: 14 unit tests in the file, 15 in
  `tacenta-core/tests/identity_expectation.rs` and 10 in
  `tacenta-core/tests/identity_responder.rs`. Vectors: 128 in five files under
  `tacenta-test-vectors/vectors/identity/` (`pair-digest.json` 38,
  `verification-number.json` 9, `identity-classification.json` 20,
  `identity-lookup.json` 14, `initiator-expectation.json` 47), the first four
  generated from the model and the fifth written by
  `generate-identity-vectors.py` with every outcome checked against the model.
  The Rust runner checks them against `tacenta-core`, and the independent reader
  reads all 128 with no failure (125 at its fourteenth pass; three were added
  after it and pass with the reader unchanged). A fuzz target of their own,
  `identity_records` (`tacenta-core/fuzz/fuzz_targets/identity_records.rs`),
  drives the classification, the lookup, the digest, the verification number
  and initiator establishment under an expectation with a fuzzed presented
  key and fuzzed records, over an honest bundle whose identity key the input
  may replace. It asserts that the lookup agrees with the classification
  record by record, that the digest does not depend on argument order, that
  a malformed expectation is refused as `MalformedRecord` and only then, that
  a refusal on the expectation draws nothing, and that a session is returned
  only for a key the expectation accepts. It does not fuzz the rest of the
  bundle (its prekeys and signatures). Like every fuzz target here, the
  hosted workflow neither builds nor runs it; `tooling/ci.sh` runs it briefly
  from its three committed seeds when `cargo-fuzz` and a nightly toolchain
  are present. Whether the nightly search on private infrastructure
  (`ASSURANCE.md`, practice 10) runs it has not been checked.
- **Where that leaves them against ADR-0008's levels.** They have no
  property test of their own (no proptest names them, in their own tests or
  in `tests/fuzz.rs`; the fuzz target's assertions run only under
  `cargo-fuzz`), and their fuzzing reaches the presented key and the records
  but not the rest of an untrusted bundle. So they meet L1 only in part: its
  unit tests, yes; its property tests, no; its fuzzing of untrusted input,
  partly, and not in the hosted workflow. Since L2 includes L1, they do not
  reach L2 either, although they have its other elements: the model states
  them, and vectors pin them that are checked against the implementation and
  read by the independent reader (`initiator-expectation.json` is written by
  a script with each outcome checked against the model, not generated from
  it). The Session row in `ASSURANCE.md` stays at L2, because a tick there
  means that the component has that kind of evidence, not that every part of
  it does, and a level is lowered only by a recorded decision (ADR-0008); the
  row says the same of these functions.
- **What is proved, and about what.** `Model.IdentityRecords` and
  `Model.InitiatorExpectation` state the same rules, and `CLAIMS.md` ("Proved
  (tier T2, in the model: identity records and the initiator's expectation)")
  claims 35 theorems about those definitions. They are about the model only.
  No theorem says that the crate's functions compute the model's, that the
  model's definitions are what the pages say, or that the model's rule
  argument `oracle.identityValid` is `Model.IdentityKey.valid` (the vector
  generator sets the one to the other).
- **The public initiator entry is an unverified hop.**
  `tacenta_core::sessions::establish_initiator` is the wrapper. It refuses a
  malformed expectation, makes the bundle's presence and canonical-key checks,
  checks the bundle's identity key against the expectation, and then calls the
  lifecycle leaf's `establish_initiator_for` with the bundle's own identity key
  as the expected one, returning what that call returns. The leaf's
  `establish_initiator` and `establish_initiator_for` are no longer re-exported
  from `tacenta_core::sessions`. The theorems about `establish_initiator_for` on
  the eight-leaf session unit (its T1 theorem, and the T3 results at the session
  it returns) are about the leaf function. That they carry over to the session
  the wrapper returns rests on reading the wrapper: it takes everything but the
  random source by shared reference, draws nothing from the random source before
  the call, and passes the leaf's session on unchanged (a refusal of the leaf's is
  passed on inside `InitiatorError::Establish`). Tests check it
  (`with_no_records_first_contact_is_the_leafs_establishment` compares draws and
  exported bytes with the leaf's own establishment, and
  `the_leaf_pin_never_fires_through_the_expectation`); no proof about the crate does.
  The theorems take no hypothesis about identity records (ADR-0009) or an
  `Expectation`, so nothing is assumed of the wrapper; what is missing is a
  theorem about it. The model proves the counterparts about the model's step
  (`Model.InitiatorExpectation.refusal_keeps_oracle`, `success_is_leaf`,
  `leaf_never_unexpected`), and nothing relates them to the crate. The test
  that compares the wrapper's result with the leaf's runs under *first
  contact* with no identity records, against the leaf's trusting
  `establish_initiator`, which passes the bundle's own key to
  `establish_initiator_for`; under *known*, or with records, the session the
  wrapper returns is not compared with the leaf's. The gate that compares the
  lifecycle's public surface with the translation
  (`check-lifecycle-translation-coverage.py`) reads two files: the Rust source
  `tacenta-core/lifecycle/src/lifecycle.rs` and the generated
  `TacentaLifecycle.lean` it is given. It reads no other Rust source, so it lists
  neither the wrapper nor `establish_responder_unattributed`, and a public entry
  added in `tacenta-core/src/sessions` does not turn it red.
  `tooling/check_authentication_boundary.py` finds such an entry by name when
  the name holds one of its verbs (`establish` among them) and requires it
  registered, but it reads signatures, not bodies, and checks nothing about
  translation.
- **The wrapper repeats the leaf's checks.** The presence and canonical-key
  checks are written again in the wrapper, with the leaf's own predicates, so
  that they come before the expectation, and the model does the same
  (`Model.InitiatorExpectation`, the header's note). If the leaf's checks change,
  the copies do not follow by themselves; the identity vectors and the tests are
  what would notice.
- **The authentication-boundary checker reads the wrapper's signatures, not its
  body.** `tooling/check_authentication_boundary.py` scans six zones, now with
  `tacenta-core/src/sessions` among them, and `AUTHENTICATION-BOUNDARY.md`
  registers `establish_initiator` and `establish_responder_unattributed` there (31
  paths in all). It checks that each is registered under its signature.
- **The responder adds no refusal.** `establish_responder_unattributed` calls the
  leaf's `establish_responder` unchanged and returns its first plaintext wrapped
  as unattributed. `attribute` releases it beside a lookup of the session's
  peer key in the records the caller gives; it cannot check that those are
  the party's records (given none, it releases the value as unattributed),
  and the leaf's `establish_responder`, which returns the plaintext unwrapped,
  is still exported. So the wrapper is a nudge, not an enforcement. Whatever the
  leaf commits, it commits. Attributing a session or a plaintext to a contact is
  the application's act (ASM-14).
- **The strength of the verification number is assumed.** About `2^100` work for
  an attacker holds only if all 60 digits are compared over a channel the
  attacker does not control, and it rests on treating SHA-256 reduced mod `10^60`
  as a random function (ASM-07; REQ-AUTH-16 is assumed). Comparing `k` digits
  costs about `10^(k/2)`.
- **Not provided.** The records themselves (their storage, integrity, rollback
  and loss), how an application attributes and shows plaintexts, device handling,
  and key transparency are not provided by `tacenta-core` or by the
  specification. Nothing proves that an identity key belongs to the person a user
  means; that is ASM-14, an assumption.
- **Not yet adopted.** Adoption by the application, FFI and SDK layers above
  `tacenta-core` is separate work; until it lands, the product does not use
  these functions.

### The Session unit's primitive contracts are totality assumptions

The eight-leaf `TacentaSessionUnit` makes the ratchet, Braid, erasure, wire,
session and lifecycle bodies concrete in one Lean namespace. The primitive
implementations remain outside that unit. The first Session proof layer names
thirteen contracts, the cap the primitive-boundary decision set until its note of 2026-10-01: ten over the
primitive boundary, `DhCodecTotal`, `DhIdentityTotal`, `DhAgreeTotal`,
`AeadOpenTotal`, `KemEncapsulateTotal`, `KemDecapsulateTotal`,
`KemCiphertextLenTotal`, `XeddsaVerifyTotal`, `XeddsaSignTotal` and
`Random32Total`; one over the
AEAD's output shape, `AeadSealBounded`, which says the call returns and that
the ciphertext and authentication tag are at most forty-eight bytes longer than the plaintext (a length
bound the framing headroom needs, so it is not a totality contract); and two
over standard-library and `zeroize` operations Aeneas leaves opaque,
`VecPopTotal` and `MessageKeyMaterialRoundTrip`. The decision record named ten
and `AeadSealTotal`; the complete translation and its T1 layer showed the
twelve, and the identity-key rule added `DhIdentityTotal` as the thirteenth;
the record carries a dated note for each. These thirteen are the contracts over
primitives. The contract records in `CLAIMS.md` (session lifecycle T1 section)
hold further totalities over the ratchets, the Braid, the Triple Ratchet and the
session layer, which this section does not list. A fourteenth, `DivCeilValue`, the
value `(a + 31) / 32` of `usize::div_ceil` at divisor 32, is a field of
`EstablishResponderContracts` that the repair of the receive decoder hypothesis
added; the note of 2026-10-01 counts it and recuts the cap at fourteen. Its separate
witness is `divCeilValue_shape_satisfiable`, and the joint model also satisfies it
(`model_DivCeilValue`); neither is a name of the coverage theorem below.

Apart from `AeadSealBounded` and `DivCeilValue`, these contracts say that the outer Aeneas `Result` returns. `DivCeilValue` also says that `usize::div_ceil` at divisor 32 returns `(a + 31) / 32`, which the decoder bound needs. They permit an
AEAD, KEM or signature check to return its ordinary inner refusal, and permit
DH agreement to return `None`. They do not say that encryption is secure,
that signatures are sound, that agreement outputs match, or that an accepted
result has the right bytes. Those value-level agreements belong to the later
refinement relation and its oracle; the totality layer alone cannot establish
them. Two of them, `AeadSealBounded` and `AeadOpenTotal`, are not only assumed: by reading they are false of the shipping
AEAD at long lengths, so the theorems that take them are conditional on a proposition that does not hold and, as stated,
say nothing about the shipping code at any length ("The clauses of `OracleOf`", the totality row).

**A KEM totality contract was false of the shipped code, and is now kept by it rather
than proved.** `Encapsulate2Total` in `BraidT1.lean`, and its copy in
`SessionUnitBraidT1.lean`, say that `encapsulate2` returns for every `EncapsState`.
`KemEncapsulateTotal`, one of the thirteen above, is a different contract: that the
boundary's `kem::encapsulate` returns on every public key, given a random source
that returns (`UnitLifecycleT1.lean`); it is not about restored state. Before
the coefficient bound in `kem/src/lib.rs` (`encapsulate2`), a state restored
from persistence, which `EncapsState::from_bytes` accepts on its length alone,
could carry `i16` ring-element coefficients outside `|c| <= 3328`, the bound
libcrux-ml-kem 0.0.10 states as a hax precondition (`requires`) of its
`ntt_multiply` and `add_message_error_reduce`; this project has not checked
that the library discharges it, and `compute_ring_element_v` and
`invert_ntt_montgomery` on that path are marked lax (the section above on
libcrux). Outside the bound the library's behaviour is undocumented: on its
portable backend an `error2` coefficient of magnitude about 31,626 or more
overflowed `i16` (`vector/portable/arithmetic.rs`, the add in
`add_message_error_reduce` and the Barrett multiply) and panicked, since this
workspace keeps overflow checks on in release; smaller out-of-bound values and
out-of-bound `r_as_ntt` returned a ciphertext; the NEON backend returned a
ciphertext for every pattern tried; AVX2 was not run. `encapsulate2` now
refuses any coefficient outside the bound before the library runs, so both
copies of `Encapsulate2Total` hold of the wrapper as an assumption about libcrux inside its stated
precondition, the state-side half of which the wrapper keeps (the `ek_vector`
side rests on `validate_ek`, which the Braid runs on a received vector and
which a tag 8 restore does not repeat). That is tested, not proved:
`kem/tests/malformed_stored_state.rs` drives fixed patterns and every one of
the 1,280 coefficient positions at the bound and one past it through
`encapsulate2`, and fails on a panic, on a ciphertext from an out-of-bound
state, or on a refusal of an in-bound one; its scan and random sweep are
informational. At the public surface,
`a_restored_session_with_an_out_of_bound_encapsulation_state_fails_closed`
(`lifecycle/src/lifecycle.rs`) exports a session that holds an encapsulation
state, overwrites that state's coefficients with `i16::MAX`, restores the bytes
through `Session::import`, and drives the restored session through `decrypt`
and `encrypt` until it refuses with `AgreementFailed`; the restored session's
own `encrypt` and `decrypt` then refuse. It needs write access to the stored
blob; with the bound disabled it fails. The session it restores holds the
encapsulation state as the responder (Braid tag 7), as does the Braid-level
test's; both reach the refusal from tag 9 through transition (11). No test
restores an out-of-bound state at tag 8 or 9, or reaches the refusal through
transitions (9) or (12). Both tests were run on this
machine on the NEON and portable backends (the portable one by building with
`LIBCRUX_DISABLE_SIMD128=1`), not on AVX2; the `rust` job's
`rust_portable_kem` step, added with this change, runs the KEM, Braid and
lifecycle tests on the portable backend and is the first hosted run of that
backend, and until it has run the portable half is a local receipt. `IncrementalKeyPair::from_bytes` is also length-only; `decapsulate`
on a key pair with out-of-range coefficients in its secret polynomials returned
on every pattern and random key pair tried, and that it never panics is not
checked.

`DhCodecTotal` is one joint contract over both opaque DH key types and all six
reachable construction, projection, derivation and equality operations. Its
non-vacuity witness interprets those types together, so the operations cannot
be justified by mutually incompatible one-function witnesses. Randomness is
scoped to the concrete `RngCore` instance supplied to an operation: a contract
over every possible trait record would be false because the trait permits a
`fill_bytes` implementation that fails.

`DhIdentityTotal` says that `is_prime_order_public` returns for every key, and
nothing more. The function is in the trusted primitive crate
(`tacenta_boundary`), so it is one of the opaque externals above, and Lean
cannot tell it from the constant `true`: replacing its body changes no theorem.
What it computes, the identity-key rule of identities-and-devices.md (Identity
keys), is **tested and pinned, not proved**. `Model.IdentityKey.valid` states
the rule from the page and is not itself proved to be the rule; the vectors
`vectors/identity/identity-key.json`, generated from it and cross-checked
against an independent program when they are written, pin 39 keys; the
differential harness compares it with `is_valid_identity_key` over the same
keys and over more than a thousand others in both verdicts; and `tacenta-core`'s
tests drive every entry point that admits an identity key and assert the refusal
kind. The refinement contract for the establishment operations binds the
model's `identityValid` oracle to the translated `is_valid_identity_key`
(`OracleOf.identityValid`, `UnitLifecycleT3.lean`); no theorem consumes that
binding yet, because no T3 statement about establishment exists, so the
binding is a statement of intent about the oracle and not an assurance.

The hypotheses and evidence records of the lifecycle T3 branch lemmas and initial-dispatch theorems
(`UnitLifecycleT3.lean`, `UnitLifecycleInitialDispatch.lean`) do not make those theorems claims.
`Translation/DispatchEvidenceVacuity.lean` proves five of the earlier records false or empty under stated
conditions, and `Translation/UnitLifecycleIntegrationScreen.lean` proves four records the integration of the session
contract branch added empty or contradictory: a consumer structure that asked every RNG state for a draw and the two
end-to-end records that contain it, and a Braid send agreement that let key generation consume one draw where the
shipped code fills a 64-byte seed. No theorem of the two modules takes any of the nine records shown false, empty or
contradictory, or the old KEM field. The dispatch theorems take per-run evidence, which can be supplied for a run
whose agreement chunk is consistent and not for a run whose chunk is not, refused or accepted; of its scoped Braid
record only the two chunk fields are decided. The oracle's restated KEM and signing clauses follow from laws read
from the source and have a model with a refused key. The restated KEM success clause binds the code only where the
model's `kemEncaps` returns `some`, so an oracle that never encapsulates meets it. The oracle's other clauses, and
the record as a whole, follow from eleven named laws that have a model ("The clauses of `OracleOf`", below); the four
clauses the `decrypt_ratchet` refinements take (`DecryptOracleOf`) follow from four of them. The
per-run records are stated as their parts, and no part beyond the draw is shown to be met. The
model's comparison of a repeated initial ephemeral was not constrained by `OracleOf` until the model decoded both strings
before agreeing; the corrected comparison is, and the code's refines it ("The repeated-initial comparison", below), but no
dispatch theorem takes that yet. `GAP-REGISTER.md`, row
`DISPATCH-EVIDENCE-VACUITY`, lists the theorems, the conditions and what closes the row. In plain words: the decrypt
lemmas cover a refused message only if the agreement chunk it carries is a codeword of one source that fits the
decoder it is fed to. When the receiving decoder already holds a chunk, a message an attacker sends with an altered
chunk falls outside them. `decrypt_ratchet` does not look at the chunk before the authentication tag, so such a
message can reach a refusal that no theorem here describes.

The integration changes what `Model/Lifecycle.lean` computes in three places, each a normative model change under
ADR-0008 rule 7. The Braid send reads two draws at `KeysUnsampled` and one at `HeaderReceived`
(`braidSendDrawCount`). KEM encapsulation refuses a key that the oracle's `kemValid` rejects before it reads a draw,
so `initiate` at such a key with no draw left returns the KEM refusal and not the ceiling. XEdDSA signing reads two
draws, and the oracle's `sigSign` takes both. The first is a correction of the model: its `sendAgreement` read one
32-byte draw at `KeysUnsampled` from #161 until this change, while `mlkem-braid.md` has said since 2026-09-11 that key
generation draws 64 bytes, and `tacenta-core` fills a 64-byte seed there. The tags `tacenta-assurance-v0.4.2` to
`tacenta-assurance-v0.4.5` contain the one-draw model. No claimed theorem takes the one-draw form; the dispatch
theorems that took it are not claims, and with the signing clause they had no model
(`braidSendTrace_conflicts_with_sigSign`). The second fixes an order the specification leaves open: the model draws
the initiator's ephemeral key before it checks the bundle's KEM key, and the check refuses before the 32 bytes of `m`
are read. `GAPS-13.md` (G13-04, under `READER-OPEN-GAPS`) records that the order is not stated, and the independent
reader chose the other order. The model follows `establish_initiator_for`.

The lifecycle model draws randomness as 32-byte entries of one ordered trace, and reads a 64-byte fill as two
consecutive entries. `RngCore` does not promise that one 64-byte fill equals two 32-byte fills; the model assumes
it. The proofs assume three laws about the shipped functions:
`SignFillsOnce64`, `GenerateFillsOnce64` and `KemShape` (`UnitLifecycleIntegrationScreen.lean`). They are read from the
source and are not proved; `tacenta-core/tests/rng_fill_counts.rs` tests them on the shipped source with a counting
random source. No vector is generated by `Model.Lifecycle.encrypt`. The session end-to-end vector
(`session-e2e.json`, produced by the project runner and not by the model) runs the shipped `Session::encrypt` against
a random source that allows exactly one 64-byte fill for the first send and none for the second
(`tacenta-test-vectors/runners/rust/src/session_e2e.rs`), so it pins the 64-byte draw of the first send. No check
relates that vector to the model; the model's examples in `Model/Lifecycle.lean` follow the same draw order with toy
values. No request of the `difftest` executable runs `Model.Lifecycle.encrypt`: `Difftest.runSession` would, through
`Model.LifecycleTrace.run`, and no request handler calls it. No test holds the `HeaderReceived` draw of the shipped
Braid to 32 bytes; it is read from `encapsulate1`.

`UnitSatisfiabilitySession.lean` binds every contract shape to the generated
constant with an `Iff.rfl`, exhibits a model for each shape, and combines all
thirteen witness names in one theorem (`all_thirteen_contracts_satisfiable`).
`check-session-satisfiability-negatives.sh` removes each of the thirteen
witnesses in turn, and requires elaboration to fail each time. The thirteen
witnesses are separate, one per contract of the first Session proof layer, so they do not show that the contracts
hold together, and one of them could not have: the witness for `VecPopTotal` was a
`Vec::pop` that returns and leaves the vector unchanged, which, given `ZeroizeTotal` and, for the second field, the blanket `Zeroize` law, makes two of the
records' fields false (`UnitSatisfiabilityRatchet.lean`). It is now the `pop` of the joint model, and its shape
carries the law that `pop` drops the last element as well as the totality. This
establishes only that the assumptions are consistent; it does not prove that the real
primitive implementations satisfy their value-level specifications. That the four contract records
hold together is the next subsection.

### The four contract records follow from an axiom base that has a model, under five laws

`EncryptContracts`, `DecryptRatchetContracts`, `EstablishInitiatorContracts` and
`EstablishResponderContracts` (`CLAIMS.md`, the session lifecycle T1 section) are the
hypotheses of the Session lifecycle theorems. A theorem whose hypothesis nothing can
satisfy is true and says nothing, and two of the four records contained such a
field until it was restated (`GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`).

**The two KDF fields of `Interp`.** Since the KDF change (ADR-0010) the KDF's bodies are translated, so two of the 49 constants
`Interp.real` interprets, `tacenta_kdf.hmac_sha256` and `tacenta_kdf.hkdf_sha256`, are definitions, not axioms. The
substitution argument this section and the ones below rest on replaces axioms only, so it covers the other 47; for the
two KDF fields what stands in its place is proof: the KDF laws the records take hold of the real definitions
(`UnitLifecycleKdf.hmacShape_real`, `hkdfShape_real`). The toy interpretations give the KDF fields functions of their
own, and how far those are the real ones is proved for one family and open for the other:
- `Interp.modelT3`, and the seven interpretations of the lifecycle screens built on it (`modelShipped`,
  `modelDecrypt`, `modelFirstReceipt`, `modelEncrypt`, `modelEstablished`, `modelFirstFrame`, `modelReply`), and
  the four `InterpO` models built from four of those by replacing `xeddsaSign` (`InterpO.modelEncrypt`,
  `modelFirstFrame`, `modelFirstReceipt`, `modelReply`; they keep the fields by construction, which no theorem
  states), give them the model's HMAC and HKDF, and those are the real definitions on every key and message (HMAC) and at every
  output length up to 8160 bytes (HKDF): `UnitLifecycleKdf.modelT3_hmac_eq_real`, `modelT3_hkdf_eq_real` and
  `toy_models_share_modelT3_kdf`. Above 8160 bytes the real HKDF refuses and `modelT3`'s returns; whether any law of
  those models reads the HKDF past that bound is not checked.
- `Interp.model`, whose KDF returns zero bytes, and the interpretations that keep its KDF fields
  (`Interp.faithful`, and those the record, headroom and oracle modules build from it) give different functions from
  the real KDF. Whether their joint laws still hold with the real KDF in place of theirs is not checked.
- The leaf and three-leaf witness files (`Satisfiability.lean`, `UnitSatisfiabilityTriple.lean`) are in the same
  position for their translations: their KDF witnesses are void bridges now, the KDF hypotheses there are proved
  (`KdfLeafAgreements`, `KdfTripleUnitAgreements`), and whether their witnesses of other hypotheses still hold
  together with the real KDF is not checked.

`check-session-satisfiability-negatives.sh` admits exactly these two definitions among
the interpreted constants and refuses a third.

**What is shown.** `UnitSatisfiabilityJoint.lean` interprets 49 constants of
`TacentaSessionUnit.lean`, 47 opaque axioms and the two KDF wrappers, translated definitions since the KDF change (ADR-0010)
(6 types, 4 constants, 39 functions; of the unit's other 39 axioms, 38 are reached
by no field, and the 39th, the error type inside `RngCore`, is reached through the type `RngCore` and is not
interpreted because no contract looks at it) in one structure, and shows that one
interpretation satisfies every field of the four records that mentions only those constants,
the two model classes and five laws about standard-library and `zeroize` operations. Each shape is bound to the
predicate it replaces by `Iff.rfl`, except that `VecRetainTotal` is bound by regrouping its conjuncts. The thirteen distinct predicates among the records' fields that are
statements about translated functions are proved from named laws (`UnitSatisfiabilityErasure.lean`,
`UnitSatisfiabilityRatchet.lean`, and `SessionBraidReceiveRepair.lean` for the bounded
`DecoderMessageTotal`). `UnitSatisfiabilityRecords.lean` proves that, at the real constants, the
axiom parts of the four records, the class `SessionUnitT1.DerivedKeysModel` and those five laws give
the four records, and that they have a model (`records_of_axiom_base`, `axiom_base_satisfiable`).

**The sense of "inhabited".** Every axiom of the unit that a record reaches is an uninterpreted constant. The
unit has 229 axioms in all: 86 uninterpreted constants (48 reached by the records, 38 not) and 143 compiler-trust
facts about the byte length of format strings, none of which mentions an interpreted constant, so replacing the
47 interpreted axioms leaves them true (the other two of the 49 interpreted constants, the KDF wrappers, are
translated definitions since the KDF change (ADR-0010); "The two KDF fields of `Interp`" above). The first of the two theorems holds, under the base, for every assignment of the
constants; the second exhibits an assignment under which the base holds. So a derivation of `False` from a record at the real constants would, after the constants are replaced by
the model's terms, become a derivation of `False` from facts that hold in the model. That last step is an
argument about derivations and not a theorem inside Lean. Making it one needs a copy of every translated body
that the record fields reach, each bound to the original by `Iff.rfl`; this is done for `Decoder::new` as an
illustration and not for the records. Read the result as "the records are not contradictory, given the
laws", and not as a statement about the Rust.

**The laws, as assumptions about the real standard-library and `zeroize` functions.** The proofs of the fields about translated
functions need five facts about opaque operations. Each is an assumption of this result, true of the real
function as documented and not checked against it by any proof here. Four are stated by no record and one by
only one.

| Law | Statement | Used by | Needed? |
|---|---|---|---|
| `LawPop` (`UnitSatisfiabilityRatchet.lean`) | `Vec::pop` of a non-empty vector returns the vector without its last element. `VecPopTotal` says only that it returns. | `SessionUnitT1.RemoveSkippedAtTotal`, `SessionUnitSpqrT1.RemoveSkippedAtTotal` (the sparse field's length claim, the classical field's key and value claims) and the three loop contracts inside `VecRetainTotal` (they terminate only because `pop` shortens), so by `EncryptContracts`, `DecryptRatchetContracts` and `EstablishResponderContracts`; and, as the field `pop` of `DecryptRatchetAgreements`, the derivation of `SessionUnitSpqrT3.VecRetainAgrees` and `RemoveSkippedAtAgrees` (`UnitSatisfiabilitySpqrSessionLaws.lean`) | A `pop` that returns `(none, v)` for every vector falsifies both removal fields, given `ZeroizeTotal` and, for the classical one, `LawBlanketU32` (`..._false_of_noop_pop`); whether every `pop` that does not shorten does is not checked. Not shown to be exactly implied by a field. |
| `LawAsMut` | `Option::as_mut` returns, at every type (the proofs use it at `Option<Chain>` only) | `SetChainsLoopTotal`, `ClearChainsLoop0Total`, through `Chains::zeroize` (same three records); and, as the field `asMut` of `DecryptRatchetAgreements`, the derivation of `SessionUnitSpqrT3.VecRetainAgrees` | Forced at `Option<Chain>` by `SetChainsLoopTotal` (`setChainsLoopTotal_forces_asMut`) |
| `LawBlanketU32` | the blanket `Zeroize` returns at `u32` | the classical `SessionUnitT1.RemoveSkippedAtTotal`, through `SkippedKey::zeroize` (`DecryptRatchetContracts`, `EstablishResponderContracts`) | Forced by that field with `ZeroizeTotal` (`ratchetRemoveSkippedAtTotal_forces_blanketU32`) |
| `TruncateTotal` (`SessionUnitErasureT1.lean`, already the hypothesis of `message_no_panic`) | `Vec::truncate` returns at `Vec<u8>` | the bounded `DecoderMessageTotal`, so `DecryptRatchetContracts`, `EstablishResponderContracts` | Not checked whether the field forces it |
| `DivCeilValue` (`SessionUnitDecoderBound.lean`) | `usize::div_ceil a 32` returns `(a + 31) / 32` | `DecoderNewTotal` and `EncoderNewTotal`, each exactly equivalent to "`div_ceil` returns at divisor 32" (`decoderNew_iff`, `encoderNew_iff`), so by `EncryptContracts` (through `EncoderNewTotal`), `DecryptRatchetContracts` and `EstablishResponderContracts` (`EstablishInitiatorContracts` has no erasure field and takes none of the five laws); stated by `EstablishResponderContracts` as `divCeilValue` and by no other | The two fields are equivalent to the weaker law, which is implied by this one |

`LawPop`, `LawAsMut` and `LawBlanketU32` are new to this ledger. The model satisfies stronger
statements than these (`pop` returns the last element, `truncate` is a prefix, `div_ceil` is ceiling division,
`as_mut` is the identity borrow, `capacity` is at least the length: `FaithfulShape`), so the witness is the real
operation on them and not a degenerate function with the weak property. The blanket `Zeroize` is modelled as the
identity, which is not what it does; only its returning is used by a law (the array, vector, pair and tuple `Zeroize` are the identity too; `UnitSatisfiabilityZeroizeScope.lean` gives a second interpretation in which the array, vector and pair ones zeroize element by element and propagate a failing element's failure, and which satisfies every shape as well). `LawPop`, `LawAsMut`, `LawBlanketU32` and `TruncateTotal` are not in any of the four contract records, and no contract
record changed for them. `LawPop` and `LawAsMut` are, however, fields of `DecryptRatchetAgreements`, so the
`decrypt_ratchet` theorems take them as hypotheses: with the contract fields `ZeroizeTotal` and the first two conjuncts of
`VecRetainTotal` they derive the two sparse agreements about translated functions (the section on the
`decrypt_ratchet` refinement below). `LawBlanketU32` and `TruncateTotal` remain assumptions of the inhabitation result
only. `DivCeilValue` is the
field `divCeilValue` of `EstablishResponderContracts`, added by the repair of the receive decoder hypothesis and counted as
the fourteenth session contract. `DecoderNewTotal` and
`EncoderNewTotal` stay fields of the records although `DivCeilValue` implies both; whether they can be removed
is not checked. `SessionUnitBraidPreserve.lean` takes one more law about a standard-library operation,
`TruncateLen` (`Vec::truncate` of `n` returns at most `n` elements), which no record states. It is recorded
in "The Braid's preservation theorems" below, with `NewMsgLen`, the corresponding law on the standalone
translation.

**The headroom records.** `EncryptHeadroom`, `DecryptRatchetHeadroom`, `EstablishInitiatorHeadroom` and
`EstablishResponderHeadroom` are the conditions on the input of the five lifecycle T1 theorems that are not contracts about
primitives, and `InvariantPreconditions` is what `invariant_gives_preconditions` concludes from `Session::invariant`. A
lifecycle theorem is vacuous if no input meets its headroom. `UnitHeadroomSatisfiable.lean` and `UnitHeadroomInvariant.lean`
show that each is met, in the sense below.

*What the records are.* The two establishment records are one bound each: `EstablishInitiatorHeadroom` is exactly
`kem_prekey.length < Usize.max` and `EstablishResponderHeadroom` exactly `last_resort_seen.length < Usize.max`
(`initiatorHeadroom_iff`, `responderHeadroom_iff`). `DecryptRatchetHeadroom` is three facts about the Triple and Braid states
and a bound on the associated data. `EncryptHeadroom` is the chain table, the associated data, the plaintext
(`102 + (plaintext.length + 48) <= Usize.max`) and, with an initial message pending, its ciphertext. Every numeric bound has the form `length + c <= Usize.max` (or `< Usize.max`) for
the length of a vector or slice, or is `max(skipped.length, MAX_SKIPPED_STORE) + MAX_SKIP <= Usize.max`, which is `3000` for at most 2000 skipped keys, and `Usize.max` is at least `2^32 - 1` at both
platform widths, so each is met at both (`usize_max_ge`, `plaintext_bound_at_widths`); no bound is a `u32::MAX` bound.

*What is shown.* A Triple state with no skipped keys and one chain-table entry, and a Braid in `KeysUnsampled`, meet the receive
record's state fields (`freshTriple_headroom`, `freshBraid_bounds`); a session over them meets `DecryptRatchetHeadroom` and
`EncryptHeadroom`, with and without a pending initial message, for any associated data and plaintext within the bounds
(`decryptHeadroom_satisfiable`, `encryptHeadroom_satisfiable`, `encryptHeadroom_satisfiable_pending`), and a bundle and a prekey
store meet the establishment records. Each record is false of some input, so none is a bound that everything meets
(`*_not_trivial`). In the Lean model a vector can have length `Usize.max`, which is what the controls use. A Rust allocation is at
most `isize::MAX` bytes, so every bound on one length holds of every real input and the controls exhibit lengths the real
operation cannot receive. That is by reading and not a theorem, because the Aeneas `Vec` carries no `isize::MAX` bound, and the
pending-message arm of `EncryptHeadroom` bounds a sum of two lengths, which that limit alone does not settle on a 32-bit target.
The fields that are facts about a state and not about a size are `ct1_bounded` and `decoders_bounded`, which `Session::invariant`
supplies. A session that passes `Session::invariant` has exactly 66 bytes of associated data (`invariant_gives_ad_length`,
given `DhCodecTotal`), so `DecryptRatchetHeadroom` holds of every such session with nothing left for the caller
(`decryptHeadroom_of_invariant`, given `Ct1LenTotal`), and `EncryptHeadroom` of such a session is exactly the plaintext bound
and the `initial` field (`encryptHeadroom_iff_of_invariant`). A session over fresh states passes `Session::invariant`, evaluated
through the translated Triple, Braid and structural checks, and meets both records (`sessionOf_invariant`,
`invariant_session_meets_both`). The invariant is not a formality: a Triple state with an empty chain table meets `ReceiveHeadroom`, and a Braid at
epoch 0 meets `ct1_bounded` and `decoders_bounded` (`emptyChain_headroom`, `epochZero_bounds`); a session that holds either one
fails `Session::invariant` (`session_emptyChainTable_fails_invariant`, `session_epochZero_fails_invariant`); and the sparse
ratchet and the Braid fail their own invariants (`emptyChainTable_fails_invariant`, `epochZero_braid_fails_invariant`).

*The sense, and the assumptions.* The lifecycle types are built from opaque types of the unit, and no closed value of any of them
exists in the real environment: Lean cannot show that `PrivateKey` is inhabited, and an interpretation in which it is empty,
which is by reading and not by a theorem here, satisfies the unit's axioms (and falsifies `DhCodecTotal`). Every witness takes values of those types as arguments, so a statement of the form "some input meets
the headroom" holds at the real constants only given those values. For `PrivateKey` and `PublicKeyBytes` they come from
`DhCodecTotal`, which all four records carry (`nonempty_privateKey_of_dhCodec`, `nonempty_publicKey_of_dhCodec`), so for a
`Session` and a `PublishedBundle` the headroom is met whenever the record holds (`encrypt_headroom_of_contracts`,
`decrypt_headroom_of_contracts`, `initiator_headroom_of_contracts`). The wrapper around the one-time prekey vector comes from
`DerivedKeysModel` (`nonempty_derivedZeroizing`), which `establish_responder_no_panic` takes as an instance argument. Those are
not extra assumptions. For a `PrekeyStore` a `kem::KeyPair` is also needed (`responder_headroom_of_contracts`), and it is the
first of three extra assumptions, none stated by any record:

| Assumption | Statement | Used by | Satisfied by |
|---|---|---|---|
| `HeadroomInhabitants` | a `kem::KeyPair` has a value | `responder_headroom_of_contracts`, `headroom_of_axiom_base`: the `PrekeyStore` the responder takes holds one, and, by reading, no field of any record produces it (`KemDecapsulateTotal` takes a key pair and does not return one; `KeyPair::generate` and `KeyPair::from_bytes` occur in no record) | the joint model (`Unit`): `model_headroomInhabitants` |
| `ValidKeyShape` | a private key exists whose public key is canonical and of prime order (`public_key`, `as_bytes` and `is_prime_order_public` agree on it) | `invariant_session_meets_both`: `Session::invariant` calls `is_valid_identity_key` on both identity keys and compares `public_key(ratchet_private)` with the ratchet's public key | the joint model: `model_validKeyShape`. Of the real primitives it is tested, not proved (rows `honest-h1` to `honest-h3` of `tacenta-test-vectors/vectors/identity/identity-key.json`, run by `tacenta-test-vectors/runners/rust/tests/identity.rs`; and, for the trusted primitives, "Trusted, not verified") |
| `OptionEqU64Shape` | `Option::eq` on two `Some` values of `u64` compares them | the same: the invariant compares the Triple's epoch plus one with the Braid's through `Option::eq` | not the joint model, which does not interpret `Option::eq`; `optionEqImpl`, a Lean function of the same type: `optionEqImpl_shape` |

Each is a statement over the opaque constants, bound to the real ones by `Iff.rfl` (`headroomInhabitants_is`, `validKeyShape_is`,
`optionEqU64Shape_is`), and satisfied, the first two by the joint model and the third by `optionEqImpl`. So the headroom
records are satisfiable in the sense of the previous paragraphs, the substitution argument, with `PrivateKey`, `PublicKeyBytes`
and the wrapper around the one-time prekey vector inhabited by the contract records, and these three statements in the base: an argument about
derivations and not a theorem inside Lean, and not a statement that the real `PrivateKey` has a value, that the real primitives
satisfy `ValidKeyShape`, or that the real `Option::eq` behaves.

*Counter ceilings, assumed.* `DecryptRatchetHeadroom` is a size record; the `decrypt_ratchet` refinement also takes counter
ceilings, which no record above holds. `UnitLifecycleDecryptRunBounds.lean` derives the run's receive bounds from
`Session::invariant` and collects the ceilings the invariant does not give in one record, `CounterHeadroom`, which is ASSUMED
per run: `events + 1 < u32::MAX` for the classical clock, `epoch + 1 < u64::MAX` for the sparse epoch, every sparse chain
counter below `u64::MAX`, and `epoch + 1 < u64::MAX` for the Braid. Each excludes a state the invariant accepts and a long
session reaches: the clock parked at `MAX_EVENTS = u32::MAX - 1`, a sparse epoch or a Braid epoch at `u64::MAX - 1`, a chain
counter at `u64::MAX`. The first is proved (`invariant_does_not_give_counterHeadroom`, at a session over fresh states with the
parked clock, under `ValidKeyShape` and `OptionEqU64Shape` of the table above and `DhCodecTotal`); the other three are by reading the sparse ratchet's and the
Braid's `invariant` documentation and are not checked. That the crate's operations reach the parked clock is the clamp's
documented behaviour and is not checked either. An exclusion is permanent for a session: once the clock parks it stays, so
every later `decrypt_ratchet` of that session is outside the theorem, and one exhausted chain counter, a send chain's included,
excludes every receive until its epoch retires. By reading only, not proved: by clause (b) of `Session::invariant`
(`tacenta-core/lifecycle/src/lifecycle.rs`, the Braid-epoch relation in `structural_invariant`) the sparse epoch equals the
Braid epoch or is one below it while the Braid has not failed, and a failed Braid is refused before the Triple step (the
terminal guard at the top of `decrypt_ratchet`), so wherever the run bounds are used the Braid epoch ceiling covers the sparse
one; the sparse field is kept because `DecryptRatchetRun.retry` asks `RetryRunBounds` of every run. The first satisfiability witness
(`counterHeadroom_sessionOf`, and the joint witness `invReal`) is a session over fresh states and exercises no ceiling away from
zero (`sparseCounters` holds vacuously there). `UnitLifecycleDecryptStates.lean` gives a second, `storedSession`, built for the
hypotheses: one stored key in each store, both classical chains open, a sparse send chain at counter 7 and receive chain at
counter 6, the clock at 5, the sparse epoch at 2 and the Braid epoch at 3, so all four ceilings are met away from zero there
(the counters 7 and 6 by `storedSession_counterHeadroom` at that state; the joint statement's `StoredKeysShape` does not fix
them). It is a session with itself: `ValidKeyShape` gives one key, so both identities are that key and the classical peer key
and stored key are our own; clause (c)'s orientation is therefore not distinguished at the responder state, and the
no-two-entries clauses of both stores hold vacuously on their one-element lists. The hypotheses
of the restated refinement hold together at it under `DecryptJointLaws`
(`decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys`); and a third, the same Triple at sparse epoch 0 beside
the held-KEM Braid, under the held witness's laws (`..._at_stored_keys_held`), where the sparse and Braid epochs are at their
least values. No witness is near a ceiling, and none of these witnesses is a state produced by establishment, by `import` or by
any operation (the ceilings at the output of `establish_initiator_for` are derived below, at counters 0 and Braid epoch 1);
at these witnesses the run carries no agreement chunk and `sparseOutputEpoch` holds vacuously. No run here consumes a stored
key: the run's header names neither (classical `n = 1` against the stored `n = 2`; sparse `(0, 1)` against `(2, 3)`), so both
match filters are empty at it (`stored_run_header_names_no_stored_key`); the match bounds are tight only for headers chosen to
name a stored key. Before that, the model's step refuses at the first agreement only if the oracle's agreement refuses the
all-zero key, which no law states and which holds by reading the X25519 boundary (`invReal_agreement_is_real`); the refusal
is proved under that premise at `invReal` (`invReal_model_refuses_of_agreement`) and at `storedSession`
(`stored_model_refuses_of_agreement`); at `heldStoredSession` it is by reading only (`held_model_refuses_of_agreement` proves it at
the held witness's own state, whose Triple is fresh). The responder and pending-initial states of that module
are shown to pass `Session::invariant` only, the responder under `DhCodecTotal` as well (for `PublicKeyBytes::from_bytes` in
`decode_ec`) and the pending state under `kem::ciphertext_len = ok n` (from `KemCiphertextLenTotal`); that the opaque
`kem::ciphertext_len` returns 1568 is not checked.
These are the successor-headroom premises that
[PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md](PROOF-BOUNDARY-HEADROOM-TARGET-DECISION.md) keeps in scope (`GAP-REGISTER.md`, row
`PROOF-BOUNDARY-HEADROOM`); whether the refinement holds without them is not checked.

*What holds these results.* Each has an axiom pin that `attest.py` requires. Nineteen of the 51 also have a
`#guard_msgs in #check` statement pin, which the build compares and `attest.py` requires to exist (`REQUIRED_STATEMENT_PINS`;
it reads a pin's message only to refuse a cut-off `⋯`, so a statement changed together with its pin's expected message is accepted). The other 32 are held by the build
and by their axiom pin alone, and the axiom pin lists axioms and not the statement, so a weaker statement of any of them that
keeps its axiom list passes every gate; `CLAIMS.md` names the 32, among them the width bound and the four controls.

*At a session `establish_initiator_for` returned.* `UnitLifecycleEstablishInitiatorShape.lean` derives, at every
successful `establish_initiator_for` output, for every input, the hypotheses above that a session over fresh states only
witnessed: `Session::invariant` (`establish_initiator_for_admissible`), all four fields of `CounterHeadroom`
(`counterHeadroom_of_established`, with no hypothesis: the classical clock and both sparse chain counters are 0, the sparse
epoch 0, the Braid epoch 1) and `SessionRefines` with one model session read off the output (`sessionRefines_established`,
`sessionRefines_established_unique`, with no hypothesis; the relation holds by definition for every session whose Braid is
`KeysUnsampled`, so what the establishment supplies to it is that Braid state, and the establishment-specific content is the
invariant and the ceilings). So at that state the ceilings are not premises; at every other state
they stay assumed as above. The invariant there takes `OptionEqU64Shape` of the table above and two more laws, ASSUMED:

| Law | Statement | Used for | Satisfied by |
|---|---|---|---|
| `DhPublicValid` | every public key `PrivateKey::public_key` returns has canonical bytes and is of prime order (`DhPublicValidShape` at the real constants) | our identity key passes `is_valid_identity_key`; the ratchet key's bytes and the pending ephemeral key are canonical | the joint model: `model_dhPublicValid`. Of the real primitive it is true by reading (x25519-dalek multiplies a clamped scalar, a multiple of 8 in `[2^254, 2^255)` and so never 0 modulo the group order, by the base point, and encodes the reduced u-coordinate; `tacenta-core/boundary/src/dh.rs`), not checked in Lean. It would be false of a `public_key` that did not reduce the u-coordinate modulo p, or that could return a point outside the prime-order subgroup (a scalar that is 0 modulo the group order, or a base point of mixed order) |
| `KemCiphertextLenOf` | a successful `kem::encapsulate` returns a ciphertext of length `kem::ciphertext_len` (`KemCiphertextLenLawShape kem::ciphertext_len` at the real constants) | the pending ciphertext's length clause | `Interp` has no field for `kem::ciphertext_len`, so the shape takes the constant as an argument, as `OptionEqU64Shape` does for `Option::eq`; the joint model, whose encapsulation returns an empty ciphertext, satisfies it at `ok 0`: `model_kemCiphertextLen`. Of the real wrapper it is true by reading (`encapsulate` returns the bytes of an `MlKem1024Ciphertext`, and `ciphertext_len` is that type's length; `tacenta-core/boundary/src/kem.rs`), not checked in Lean. It would be false if `encapsulate` and `ciphertext_len` used different ML-KEM parameter sets, or if `encapsulate` returned the ciphertext with framing or truncation |

That the success case is inhabited is shown under the axiom part of the initiator contract record and one more statement,
`InitiatorSuccessShape` (a self-equal valid key on which some signature verifies for every message and every agreement is
contributory, and a KEM key on which encapsulation succeeds), assumed; the joint model satisfies it with the two laws
(`establishment_hypotheses_satisfiable`), in the substitution sense above. Of the real primitives it holds by reading, not
checked: a key whose private half is known signs every message, agreement with a prime-order key is contributory because a
clamped scalar is never 0 modulo the group order, and a valid ML-KEM-1024 public key encapsulates. The witness bundle uses one
key as identity key and signed prekey and has no one-time prekey; the success branch with a one-time prekey is not shown
inhabited. The model session is read off the output, not shown to be `Model.Lifecycle.establishInitiator`'s.

The premises of the composed results (`established_initiator_decrypt_refines`) hold together: at the real constants under the
decrypt laws `DecryptJointLaws K dh`, the initiator contract axioms, `InitiatorSuccessShape` and the two laws
(`established_decrypt_hypotheses_jointly_satisfiable`), and those shapes hold together in one interpretation,
`Interp.modelEstablished` (`established_decrypt_laws_model`), which is `Interp.modelDecrypt` with a constant canonical public
key: `Interp.modelDecrypt`, the model of `DecryptJointLaws`, does not satisfy `DhPublicValidShape`, since its public key is the
private key's bytes. Both models are toys and show nothing of the real primitives.

The success arm at this state is reached in an honest run through a copy of the session:
`tacenta-core/tests/restored_initiator_receives_reply.rs` exports the session `establish_initiator` returned, lets the
initiator send and the responder reply, restores the export and decrypts the reply, on 20 seeds. That is a test on the seeds
it tries, not a proof, and it says nothing about whether restoring an older snapshot is safe for an application. A session
value never copied leaves this state at its own first `encrypt`. The composed results relate success and refusal alike to the
model step (`StepRefines`: result, post-state and draws left; on a refusal the model's `decryptRatchet` keeps the session,
`Model.Lifecycle.decryptRatchet_refusal_keeps_session`), for a ratchet-type frame whose agreement chunk, if any, meets
`IncomingChunkRefines`, with a draw left; that chunk premise excludes some frames a sender who is not honest can send
(`CLAIMS.md`, the section on the established initiator).

*A restored session: acceptance against continuation.* `UnitLifecycleRestoredSession.lean` starts from the bytes
`Session::import` accepted. Of what the next operation consumes, acceptance gives only the invariant, proved with no
hypothesis: every accepted session passes `Session::invariant` (`import_ok_gives_invariant`). What the next operation also
consumes is not given by acceptance and stays a premise: the four counter ceilings (`CounterHeadroom`, stated for every
session, so at every accepted import, as the decidable `headroomCheck`, `counterHeadroom_iff_check`; the parked classical clock passes the invariant,
`invariant_does_not_give_counterHeadroom`, and `import` checks nothing about counters beyond the invariant, as its Rust
documentation says, "a property whose check belongs at the use site"), and the scope `RestoredScope` (Braid in
`KeysUnsampled` or `Failed`). Outside the scope no relation to a model session is claimed: a restored key pair or
encapsulation state has no model value at the wrapper's KEM model, and a restored encoder or decoder has no history for
`EncoderRefines`/`DecoderRefines`; so a restored Braid in any of the other ten states is not covered by the restored
results. The scope is narrow in practice: the first `encrypt` from `KeysUnsampled` moves the Braid to `KeysSampled`
(`tacenta-core/braid/src/lib.rs:706-724`), a responder starts in `NoHeaderReceived` (`lib.rs:420-428`), and a Braid returns to
`KeysUnsampled` only on the side that sent the last ciphertext, when the next epoch begins (`lib.rs:1355-1368`). So the
restored results cover a snapshot taken on the side holding `KeysUnsampled` before its first send in that epoch (at epoch
1, the established initiator), and a failed session; most snapshots taken mid-conversation are out of scope. That `import` of the bytes `export` writes returns every established initiator session itself
(`export_import_established`), so that the copy is in scope, meets the ceilings and receives under the model's step given
the caller's boundary records, trace equation, chunk relation and draw (`restored_established_initiator_decrypt_refines`),
takes six more laws besides the establishment's three, nine in all, ASSUMED:

| Law | Statement | Used for | Satisfied by |
|---|---|---|---|
| `ZeroizingVecRoundTrip` | `Zeroizing::new` then `Zeroizing::deref` on a byte vector returns it (`ZeroizingVecRoundTripShape` at the real constants) | reading the leaf encoders' output back out of its wrapper | `Interp.model` (`model_zeroizingVecRoundTrip`). True of the `zeroize` crate by reading (`Zeroizing` is a transparent wrapper whose `deref` returns the wrapped value). It would be false of a wrapper that copied or transformed the value on construction or read |
| `OptionBranchSome` | `Option::branch` on `Some x` continues with `x` (a shape over the constant, which the translation declares without a body) | the session-level `take_len_prefixed` and `PendingInitial::from_bytes` | `optionBranchImpl`, the standard library's definition (`restored_laws_model`). True of `core` by reading (`Some(v) => ControlFlow::Continue(v)`). It would be false only of a different `Try` implementation for `Option` |
| `VecAsSlice` | `Vec::as_slice` returns the vector's slice view (a shape over the constant) | `import`'s canonical re-encode check | `vecAsSliceImpl` (`vecAsSliceImpl_shape`). True of `alloc` by reading. It would be false of an `as_slice` that returned anything other than the vector's elements in order |
| `DhPrivateBytesRoundTrip` | `PrivateKey::to_bytes`, read out of its `Zeroizing`, then `PrivateKey::from_bytes` returns the key (`DhPrivateBytesRoundTripShape` at the real constants) | the ratchet private key comes back from the exported bytes | `Interp.model` (`model_dhPrivateBytesRoundTrip`). True of `tacenta-core/boundary/src/dh.rs` by reading (in x25519-dalek 2.0.1, the version `Cargo.lock` pins, `StaticSecret::from` stores the 32 bytes as given and `StaticSecret::to_bytes` returns them). It would be false if `to_bytes` returned something other than what `from_bytes` reads, and, as an equality of opaque values, it says the rebuilt key is the same key, which a Rust test can only check by its behaviour |
| `DhPublicBytesRoundTrip` | `PublicKeyBytes::as_bytes` then `PublicKeyBytes::from_bytes` returns the key (`DhPublicBytesRoundTripShape` at the real constants) | the two identity keys and the pending ephemeral key come back; the associated data's length | `Interp.model` (`model_dhPublicBytesRoundTrip`). True by reading (`PublicKeyBytes` wraps its 32 bytes; `from_bytes` wraps, `as_bytes` unwraps). It would be false of a `from_bytes` that normalised its input |
| `KemCiphertextLenBound` | `kem::ciphertext_len` returns at most 65536 (`KemCiphertextLenBoundShape` at the real constant) | with `KemCiphertextLenOf`, the pending ciphertext's length prefix and the size arithmetic of `export` do not wrap | `ok 0`, the constant of the established-initiator model (`model_kemCiphertextLenBound`). True by reading (`ciphertext_len` is the length of an ML-KEM-1024 ciphertext, 1568 bytes; `tacenta-core/boundary/src/kem.rs`). It would be false of a parameter set with ciphertexts over 64 KiB |

The six laws hold together with `DhPublicValid`, `KemCiphertextLenOf` and `OptionEqU64Shape` in one interpretation
(`restored_laws_model`). The whole premise list of the composition with `decrypt` (the decrypt laws, the initiator contract
axioms, `InitiatorSuccessShape` and the nine laws) also holds in one interpretation, `Interp.modelEstablished`
(`restored_decrypt_laws_model`), and at the real constants under those laws every field of `RestoredDecryptHypotheses` can
be filled at once (`restored_decrypt_hypotheses_jointly_satisfiable`). Both are in the substitution sense above; they show
nothing of the real functions. The round trip is proved
for the shape an established initiator session has (`CodecShape`: Braid `KeysUnsampled` below epoch `u64::MAX`, no stored
skipped key, one sparse chain-table entry with both chains, a pending initial message, no established ephemeral, both
variable-length fields at most 65536 bytes); a session of another shape is not covered, including a later session with
stored keys, a responder, and a Braid in any other state. `Session::invariant` alone does not give the epoch bound: a
`KeysUnsampled` Braid at epoch `u64::MAX` passes the Braid's invariant (`epoch >= 1`) and is refused by its reader, as
`session-persistence.md` states; the operations never reach that epoch, and the established session is at epoch 1. Every
statement that names `export` or `import` lists one compiler-trust axiom from the `toStr` of a panic message in the
generated `export` (`by decide +native`), not from the argument (`CLAIMS.md`).

*The first `encrypt` at a session `establish_initiator_for` returned.* `UnitLifecycleEstablishedEncrypt.lean` composes the
public `encrypt` with every establishment output, through the dispatch layer's encrypt route, and derives that route's state
premises there: the relation (by definition at the `KeysUnsampled` agreement), `EncryptHeadroom` for every plaintext of at
most `Usize.max - 65770` bytes (under `DhCodecTotal`, `KemCiphertextLenOf` and `KemCiphertextLenBound`), the two Triple
condition records (no hypothesis) and the counted draw record of the Braid send. The result relates the call's result,
post-state and draws left to the model's step (`established_initiator_encrypt_refines`) and names the two outcomes at that
state, key generation refusing or the initial message wrapping the first ratchet frame, each consuming two draws
(`established_encrypt_outcomes`). After a success the four counter ceilings hold, the session is related to the model's next
session at a `KeysSampled` agreement (not by definition: its encoder half is derived from the code's send under `ErasureAgrees`, its key-pair half is the content of `KeyGenSeededFor`), and the session passes
`Session::invariant` (`established_encrypt_successor_admissible`). The boundary records stay the caller's: the Braid and
Triple send records, `AeadSealBounded`, `DhCodecTotal`, `DerivedKeysModel`, `OracleOf`, `DhCodecOf`, `CodewordViewSendOf`
and three `zeroize` round trips, as for the conditional route; and the KEM agreements of the successor's invariant,
`KemLenAgrees` and `ValidateEkAgrees`, which the `decrypt` refinement takes as well, with `DivCeilValue`. Two laws are new,
ASSUMED:

| Law | Statement | Used for | Satisfied by |
|---|---|---|---|
| `KeyGenSeededFor` | from every source state whose trace holds two draws, `IncrementalKeyPair::generate` leaves the trace without them and answers as the model's `K.keyGen` does at their little-endian value: either it returns a key pair whose `header` is the model's seed followed by the model's hash of it and the vector, whose `ek_vector` is the model's vector and whose `decapsulate` answers as the model's does for every ciphertext pair of the model's sizes, or it refuses and so does the model's key generation (`KeyGenSeededForShape` at the real constants; the key-generation clause of `KemAgreesFor` with its randomness fixed to the two draws the model counts, `braidSendDrawCount`) | the counted draw record's trace and post-state clauses, so the RNG relation of the first send rests on this law and the run's trace equation and two draws, not on a record about the run's Braid send; the successor's key pair having the header key generation returned | the joint model `InterpO.modelEncrypt`, whose key generation fills one 64-byte seed from the source and returns its little-endian value as the key pair (refusing 0), at the toy KEM `toyKemR`: `modelEncrypt_keyGenSeeded`. Of the real wrapper, by reading: `IncrementalKeyPair::generate` fills one 64-byte seed (`KEY_GENERATION_SEED_LEN`, `tacenta-core/kem/src/lib.rs`) and computes the pair from it alone, so a model KEM read off the wrapper at those bytes (as `wrapperKem` is, `UnitKemWrapperModel.lean`) is a candidate `K`; that `KeyGenSeededFor wrapperKem` follows from the wrapper laws together with `GenerateFillsOnce64` (one 64-byte fill and nothing else) and a 64-byte fill law of the caller's source is not checked (the wrapper laws alone give some 64-byte seed, not the source's first 64 bytes). It would be false of a key generation that read other than 64 bytes, read them in another order than the trace's, or depended on anything but those bytes; and for a model `K` whose key generation is not the code's at those bytes (then false for that `K`, not of the code) |
| `KeyGenSizesOf` | the model KEM's key generation returns a 32-byte seed and a vector of `K.ekSize` bytes, and its hash of them is 32 bytes | the successor's `key_pair_valid` (the lengths `ValidateEkAgrees` asks for) and its encoder being sized for `HEADER_LEN + MAC_LEN` (96) bytes | `toyKemR`: `toyKemR_sizes`; and the KEM model read off the wrapper, under the wrapper laws `WrapperKemLaws` (assumed): `keyGenSizes_wrapperKem`. A statement about the model `K`, not about the code: true of a `K` with the layout of an ML-KEM-1024 header (seed and hash, 32 bytes each). It would be false of a model KEM of another layout, which then does not describe the wrapper's 64-byte header |

The premise lists hold together at the real constants under the decrypt laws, the initiator contract axioms,
`InitiatorSuccessShape`, `DhPublicValid`, `KemCiphertextLenOf`, the extra laws `EncryptExtraLaws` (the laws `OracleOf` is
derived from, the axiom part of the encrypt contract record, `KeyGenSeededFor` at the byte-stream source, the message-key
round trip, `KemCiphertextLenBound`) and, for the successor, `KeyGenSizesOf`
(`established_encrypt_hypotheses_jointly_satisfiable`, `established_encrypt_successor_hypotheses_jointly_satisfiable`); and
all of those laws, with the six laws of the restored session's round trip, hold in one interpretation,
`InterpO.modelEncrypt` (`established_encrypt_laws_model`). `Interp.modelEstablished` does not serve, by reading its
definition (not stated as a theorem): its key generation reads nothing from the source, so the trace clause of
`KeyGenSeededFor` fails there (the planted fault that makes the new model's key generation leave the source is refused in
`genFill_answers`), and its encapsulation does not have the form `OracleOf`'s KEM law asks for; the new interpretation changes
those two fields, keeps the rest, and adds a signing function.
Both arms of the first send are reached under those laws (`established_encrypt_success_reachable`,
`established_encrypt_refusal_reachable`, `established_encrypt_successor_reachable`): the success arm where the model's key
generation answers at the source's bytes, the refusal arm where it refuses; `toyKemR` refuses at the all-zero seed and
answers elsewhere, so both happen in the model. **The refusal arm is not reachable through the shipping wrapper, by
reading** (not checked in Lean): `IncrementalKeyPair::generate` maps only `inc::generate_key_pair`'s `Err` to its own
(`tacenta-core/kem/src/lib.rs:93-105`), and in libcrux-ml-kem 0.0.10, the version `tacenta-core/Cargo.lock` pins, that
function's only error is an output buffer shorter than the key pair: its documentation (`src/mlkem.rs:213-217`) says the
buffer must be `key_pair_len()` bytes and the function errs otherwise, the serialised generation ends in `KeyPair::to_bytes`
(`src/ind_cca/incremental.rs:148-178`), whose one check is `key.len() < Self::num_bytes()`
(`src/ind_cca/incremental/types.rs:377-383`), and the wrapper always passes a buffer of exactly `inc::key_pair_len()` bytes.
So under `KeyGenSeededFor` a `K` faithful to the shipping wrapper never refuses at the drawn value, the premise of
`established_encrypt_refusal_reachable` cannot hold at such a `K`, and the refusal effects proved here belong to a path that
is dead in the shipping code. The refusals `encrypt` can reach later in a session (the terminal guard at a `Failed`
agreement, the Triple's `NoSendingChain` and `ChainExhausted`) are shown not to occur at this state and are not covered. The
model is a toy and shows nothing of the real primitives.

What these results do not cover: the responder's receipt of the frame (`establish_responder`'s inner receive is related to the model at
the session it builds, below, but this frame is not shown to reach it; initial-frame `decrypt` is not covered anywhere), so send → receive stays open on the responder's side; a second `encrypt`
or the next `decrypt` on the session that sent (its session-side premises are derived, the calls are not composed); a copy of
the post-send session restored by `import` (its agreement holds a key pair, outside `RestoredScope`); a random source with
no state of its own, such as `OsRng`.

*At the session `establish_responder` hands to its inner receive.* `UnitLifecycleEstablishResponder.lean` composes the
public `establish_responder` for every input: each return is a refusal before the inner receive (store and random source as
given), a refusal of the inner `decrypt_ratchet` (store as given), or that receive's success with a named store commit
(`establish_responder_cases`, no hypothesis). At the session the call builds, for every input that reaches the inner
receive, it derives `Session::invariant` (`responder_prepared_invariant`), all four fields of `CounterHeadroom`
(`counterHeadroom_responder_prepared`, with no hypothesis: clock 0, sparse epoch 0, both chain counters 0, Braid epoch 1) and
`SessionRefines` with a model session read off it (`sessionRefines_responder_prepared`), so the `decrypt_ratchet` refinement
applies to the inner call. The invariant there takes `DhPublicValid` (the table above), `OptionEqU64Shape`, the value law
`DivCeilValue` of `usize::div_ceil` (`GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`) and the `HEADER_LEN` bound
`HeaderLenTotal`, a field of the decrypt contracts; no new law. The relation's Braid half is the constructor's refinement
(`responder_refines`) under the Braid agreements the decrypt records carry and `DivCeilValue`. The model session is read off
the code's session, with the model's initial responder Braid; it is not shown to be the session
`Model.Lifecycle.prepareResponder` builds. No hypothesis about the prekey store is taken: `PrekeyStore::invariant` is not used.
The run's chunk relation, `HonestChunk` (`honestChunk_responder_iff`: a header chunk of epoch 1 from a 96-byte message), the
trace equation and the draw are the caller's, asked of every parts value of the input; an attacker chooses the chunk.

That the outcomes are not about an empty set is shown at the real constants under two more statements, ASSUMED, used for
inhabitation only (no theorem about every input takes them):

| Statement | Says | Used for | Model, and when it would be false |
|---|---|---|---|
| `ResponderSuccessShape` | the base point's bytes decode to a public key with those bytes, of prime order, with which every private key agrees contributorily; some KEM key pair decapsulates some ciphertext of at most 4096 bytes; the zeroizing one-time pool's type has a value | an input reaching the inner receive (`responder_prepared_inhabited`), the `NonContributoryAgreement`, `ReplayedLastResort` and `LastResortRecordFull` refusals, the joint statements | `Interp.modelEstablished`, together with the decrypt laws, the responder contract axioms, `DhPublicValidShape` and `ZeroKeyShape` (`responder_route_laws_model`: its public-key check accepts every key, its agreement refuses only the zero key, its decapsulation always returns). Of the real primitives it holds by reading, not checked in Lean: `PublicKeyBytes::from_bytes` keeps the bytes, `u = 9` is a canonical point of the prime-order subgroup, a clamped scalar is never 0 modulo the group order so agreement with it is contributory (`tacenta-core/boundary/src/dh.rs`), and ML-KEM-1024 decapsulation of a ciphertext of the right length returns a key, by implicit rejection. It would be false of a decapsulation that refused a ciphertext of the right length, or of an agreement that refused a prime-order key |
| `ZeroKeyShape` | the all-zero public key's agreement refuses for every private key | the `NonContributoryAgreement` refusal and the inner refusal reached (`responder_route_inner_refusal_reachable`) | the same model, in the same theorem (`responder_route_laws_model`), whose agreement refuses the zero key. Of the real boundary it holds by reading (`agree` returns `None` for a non-contributory, all-zero output, which `u = 0` gives for every scalar), not checked in Lean. It would be false of an `agree` that returned the all-zero output |

The premises of the composed result (`establish_responder_refines`) hold together at the real constants under the decrypt laws,
the responder contract axioms, `ResponderSuccessShape` and `DhPublicValid`, at an input that reaches the inner receive
(`responder_route_hypotheses_jointly_satisfiable`), and with `ZeroKeyShape` the inner refusal is reached there
(`responder_route_inner_refusal_reachable`). Every law and shape of those premise lists, and of the reached refusals, holds
together in `Interp.modelEstablished` (`responder_route_laws_model`; the contracts of `establish_responder_no_panic` follow
from the axiom part and the decrypt laws' `StdLaws`), a toy that shows nothing of the real primitives. The refusals
`Decode(TooShort)`, `UnknownPrekeyId` and `LegacyLastResortRecord` are stated over every store (of a stated shape for the
last two); no store value is derivable in Lean without `ResponderSuccessShape`. Six byte-list lemmas of that module are
proved with `simp` (using `propext`) rather than `decide` (using no axiom) because `attest.py`'s pin reader reads only the
form "depends on axioms: [...]" and not "does not depend on any axioms"; that is a limit of the tool, to be fixed there, and
not a change to what the results trust. **Not shown:** a success of the whole call:
no input is exhibited at which the inner `decrypt_ratchet` succeeds (`establish_responder_at_parts` makes the call's success
exactly the inner receive's success with the commit returning); honest successes are tested only
(`tacenta-core/tests/full_session.rs` and the other responder tests). Not shown reached: `BadEncoding` (by reading not
reachable once `decode_initial` accepted, since its canonical-key checks precede `decode_ec`'s; not checked in Lean),
`Handshake(InvalidIdentityKey)` and `Kem` (the model's prime-order check and decapsulation accept every input, so a statement
that makes them refuse could not be shown satisfiable together with the others there). Which entry a removal from a one-time
pool takes is not stated (`GAP-REGISTER.md`, row `E2E-03`). The successor the call returns is not shown to pass the
invariant, and nothing is shown here of the initiator's frame (the next paragraph), the plaintext or the responder's next operation.

*At the initiator's first frame.* `UnitLifecycleResponderFirstFrame.lean` feeds the bytes the first `encrypt` at an
`establish_initiator_for` output returns to `establish_responder`, at a responder store whose `publish` returned the bundle the
initiator used and an identity whose public key is the store's identity key. There, only the three refusals the store decides
remain (the legacy marker on the last-resort key, the handshake's fingerprint already recorded, a non-empty record whose count for the key, `last_resort_seen_for`, has reached
`MAX_LAST_RESORT_SEEN`), and only
when the bundle names the last-resort key; otherwise the call reaches the inner receive at a session whose shared secret is the
initiator's (`responder_first_frame_prepares`, `responder_first_frame_admissible`, composed with the first send in
`first_send_responder_prepares`; it and the reach, `first_send_responder_reachable`, list no compiler-trust axiom). One law, one premise about the run and
one hypothesis about the store are new:

| Statement | Kind | Says | Used for | Model, and when it would be false |
|---|---|---|---|---|
| `DhAgreeSymmetric` | law, ASSUMED (`DhAgreeSymmetricShape` at the real constants) | for private keys `a`, `b` whose public keys are `pa`, `pb`, `PrivateKey::agree a pb` returns what `agree b pa` returns | the responder's four agreements are the initiator's, so the two shared secrets are equal and the responder's contributory checks pass (`shared_secret_symmetric`) | `InterpO.modelFirstFrame` (`modelFirstFrame_symmetric`), whose public key is the base point for every private key and whose agreement returns the public key it was given unless it is the zero key: a toy. True of the boundary by reading (`tacenta-core/boundary/src/dh.rs`, X25519 through x25519-dalek: both sides compute the u-coordinate of the product of the two clamped scalars and the base point, and the boundary refuses the all-zero output on both sides); not checked in Lean. It would be false of a DH whose two directions differ, of a boundary that clamped or validated on one side only, and of one that refused a non-contributory result on one side only |
| `FirstKemAgrees` | premise about the run, not a law | the KEM key pair the store holds under the identifier the bundle names decapsulates the initiator's ciphertext to the secret the initiator's encapsulation returned | the responder's decapsulated secret is the initiator's | holds in the reach's run (`first_send_responder_reachable`), from `FirstFrameSuccessShape`. Deliberately not a law: ML-KEM decapsulation of an honestly encapsulated ciphertext fails with a small probability (FIPS 203), and the wrapper's implicit rejection then returns another secret rather than an error, so a statement for every run would be false of the real primitive. Were it to fail, by reading the responder's inner receive would refuse `Aead`, not `Kem` (next paragraph); not shown |
| `PrekeyIdsDistinct` | hypothesis about the store, named | the identifiers the store holds (signed prekey, KEM key, previous ones, the one-time curve and KEM entries) are distinct and none is `ABSENT_ID` | the KEM lookup and the one-time lookup find the entries `publish` named (`u32_index` and `peek_one_time` return the first occurrence; `ABSENT_ID` names no key) | holds at the reach's store (`reachStore_distinct`). It is what `PrekeyStore::invariant`'s identifier loop checks (with the bound by `next_id`), but that the invariant gives it is not checked: the invariant reads the pools through `IntoIterator for &Vec`, which the translation leaves opaque and for which no law is in the tree. It would be false of a store holding a repeated identifier (then the lookup can find another entry than the one published) |

One more statement is assumed for inhabitation only, as `ResponderSuccessShape` above; no result about every input takes it:

| Statement | Says | Used for | Model, and when it would be false |
|---|---|---|---|
| `FirstFrameSuccessShape` | over an interpretation and two functions it has no field for (`KeyPair::public_key`, `Vec::is_empty`): a private key, given by its bytes, whose public key has canonical bytes, is of prime order, equals itself, has a verifying signature for every message and agrees contributorily with every private key; a KEM key pair with a public key and one byte stream at which encapsulation to it returns a ciphertext and a secret the pair decapsulates back; a wrapper holding the empty one-time pool; `Vec::is_empty` true on an empty vector | the run of `first_send_responder_reachable`: a store from that key and pair, its published bundle, a successful establishment against it, a first send, and the responder reaching the inner receive | `InterpO.modelFirstFrame` with an empty public KEM key and `Vec::is_empty` as an emptiness test (`first_frame_laws_model`). It would be false of a signature scheme with a key on which no signature verifies, of an agreement that refuses some private key with that public key, of a KEM whose decapsulation recovers no encapsulation at any stream, and of a `Vec::is_empty` that says an empty vector is not empty |

Every law and shape of those premise lists (the decrypt laws, the initiator and responder contract axioms,
`InitiatorSuccessShape`, `ResponderSuccessShape`, `ZeroKeyShape`, `DhPublicValidShape`, the ciphertext-length law, the encrypt extra
laws, the six restore laws, the encrypt branch's size law and seeds, `DhAgreeSymmetricShape` and `FirstFrameSuccessShape`) holds
together in `InterpO.modelFirstFrame` (`first_frame_laws_model`), a toy that shows nothing of the real primitives. The encrypt
branch's joint model satisfies `DhAgreeSymmetricShape` too, but only because every public key there is the zero key and the
agreement refuses it, so no establishment against a published bundle succeeds there; that is why the new interpretation changes
the public key and the agreement. **Not shown there:** that the inner `decrypt_ratchet` succeeds on the first frame or which
plaintext it returns (the next paragraph, under two further laws); the responder's successor, its invariant and its draws (the
next paragraph relates the successor and pins the draws; the invariant is not shown); any later message; that `PrekeyStore::invariant` gives `PrekeyIdsDistinct`.

*The responder's first receipt.* `UnitLifecycleResponderFirstReceipt.lean` continues on the same bytes. Past the store's
refusals, the call returns exactly one of `Handshake(NonContributoryAgreement)` (the responder oracle refuses the agreement
of its draw with the initiator's ratchet key), `Aead` (it refuses to open the initiator oracle's seal of the plaintext), each
with the store as given and one draw taken, or what that open returns (`responder_first_frame_outcomes`,
`initiator_first_send_responder_outcomes`). Under the two laws below it returns the plaintext the initiator encrypted, takes
one draw and commits the store (`responder_first_frame_succeeds`, `initiator_first_send_responder_receives`; none of these
four, the inner-receive results and the reach lists a compiler-trust axiom: the decrypt refinement's nine `native_decide`
constants are kernel proofs since 2026-10-21).
The first message key agrees on both sides by computation over the model's key derivations; no new law is used for it (the
code's root-key step is related to the model's under the KDF agreement the decrypt refinement already takes, `HkdfAgrees`). Two laws
and two premises about the run are new:

| Statement | Kind | Says | Used for | Model, and when it would be false |
|---|---|---|---|---|
| `AeadRoundTrip` | law, ASSUMED (`AeadRoundTripShape` at the real constants) | for keys of 32, 32 and 16 bytes, a plaintext of at most `Usize.max - 48` bytes and associated data, if `aead::encrypt` returns a ciphertext then `aead::decrypt` of it with the same keys and associated data returns `Ok` of the plaintext | the responder's oracle opens the initiator's oracle's seal of the first frame to the plaintext (`aead_open_sealed`), so the inner receive succeeds | `InterpO.modelFirstReceipt` (`modelFirstReceipt_aeadRoundTrip`): the toy seal puts a zero byte in front and the toy open removes it; a toy that authenticates nothing. True of the boundary by reading on a 32-bit target, where memory allows (`tacenta-core/boundary/src/aead.rs`: AES-256-CBC with PKCS#7 padding, then HMAC-SHA256 over the associated data and the ciphertext, appended; open recomputes the tag over the same bytes, compares, decrypts and unpads); not checked in Lean. False of it by reading on a 64-bit target built with overflow checks: the law bounds the plaintext but not the associated data, and with `2^61` bytes of associated data and an empty plaintext the seal returns (its in-tree SHA-256 wraps the bit length, and its one copy of `ad ‖ ct` stays below `isize::MAX`) while the open panics in `sha2` (the totality row). So, as stated, a result that takes it says nothing about the shipping code built that way, at any length. From a reading of their statements, the results that take it are `aead_open_sealed`, the first-frame receipt (`initiator_first_send_responder_receives`, `responder_first_frame_succeeds`), the reply (`initiator_first_send_responder_replies`), the reply receipt (`initiator_receives_reply` and its two outcome forms), the second message, send and receipt (`initiator_sends_second_message`, `initiator_second_send_after_reply`, `responder_receives_second_message`), the second reply (`responder_sends_second_reply`), the repeats (`initiator_repeated_reply_refused`, `initiator_first_send_responder_repeat_refused`), the tampered reply (`initiator_refuses_tampered_reply`), the successor and preservation results built on these, and the reach witnesses of these routes. It would be false of an AEAD whose tag on opening covers other bytes than on sealing, of a padding the decrypter rejects, of a key-dependent or randomised tag that open cannot recompute, or of a seal that truncates. It says nothing about forged or altered ciphertexts: no authenticity law is assumed, so no theorem here shows a tampered frame refused |
| `DhAgreeContributory` | law, ASSUMED (`DhAgreeContributoryShape` at the real constants) | for every private key `a` and every key `b` whose public key is `pb`, `PrivateKey::agree a pb` returns `some` | the responder's fresh ratchet key agrees with the initiator's ratchet key (`responder_candidate_agreement`), so the inner receive does not refuse `NonContributoryAgreement` | `InterpO.modelFirstReceipt` (`modelFirstReceipt_contributory`), whose public key is the base point and whose agreement refuses only the zero key: a toy. True of X25519 by reading (a clamped scalar is a multiple of the cofactor and not a multiple of the group order, and `public_key` returns a point of the prime-order subgroup, so the product is not the identity and the boundary's all-zero check in `boundary/src/dh.rs` passes); not checked in Lean. It would be false of an agreement that is all-zero against some honestly generated key, of a `public_key` that can return a small-order point, or of a boundary that refuses on another condition |
| trace premise | premise about the run | the responder's source's trace is its oracle's draws and holds a draw | the inner receive's candidate draw (the refinement takes it); without it the model refuses `ceiling` | holds in the reach's run, at the byte-stream source with 64 bytes. A source with no state of its own, such as `OsRng`, is outside the statements about draws; a real `RngCore` does not run dry, so the empty trace is a property of the trace interpretation, not of the code |
| `EstablishResponderHeadroom` | store bound, the premise of `establish_responder_no_panic` | the replay record has room for one more entry | the whole call's success (the commit's append on the last-resort path) | holds in the reach's run (an empty record); not derived from the store's invariant |

The successor relation is to the model's step at a codeword view that reads the received codeword as the initiator's header
source (`attributedView`); the proof shows that the received codeword is a codeword of that source (the codeword half of the
chunk relation is derived; the erasure code is systematic, so codeword index 0 carries the source's first 32 bytes and the derived half fixes only those; the other 64 bytes of the source in the successor's model decoder (the hash and the header MAC) come from the attribution), and the view constrains only the model session the successor is compared against, not the
bytes, the store, the draws or the call's result. `KeyGenSizesOf` of the initiator's oracle's KEM (the encrypt branch's law)
gives that source its 96 bytes. The two oracles need not be equal. The initiator's emission of the header's second chunk does
not need their Braid KEMs to agree (the second-send paragraph below). By reading, completing the header (the responder's
receipt of the initiator's later chunks) checks only its MAC under the shared authenticator and needs no KEM relation; the
first step at which both parties' KEMs act on one key pair is the responder's first sampling send, whose `encapsulate1`
(model `encaps1`) takes the initiator's header seed and hash and can refuse; the hash check of the completed encapsulation
key follows; no theorem states either. The responder's `encrypt` of its reply needs no KEM relation either:
its agreement waits for the header, and neither the code's send nor the model's reads randomness or the KEM there (the
reply paragraph below), and neither does the initiator's receipt of the reply: at its `KeysSampled` agreement the code's
receive (by reading) and the model's change state only on a `Ct1` chunk (the reply receipt paragraph below). On `Kem`: `FirstKemAgrees` stays a premise. By reading,
an honest-ciphertext decapsulation failure returns another secret under FIPS 203 implicit rejection rather than an error, so
the two shared secrets would differ and the refusal observed would, barring an HMAC collision, be the inner `Aead`, store as given and one draw taken,
not `Kem`; this is argued from the reading only and is not shown. Every law of the premise lists, with the first-frame
laws, holds together in `InterpO.modelFirstReceipt` (`first_receipt_laws_model`), the first-frame joint model with the toy
seal and open (the first-frame model's seal returns the empty vector, so `AeadRoundTripShape` is false there); a toy that
shows nothing of the real primitives. **Not shown:** that a tampered or foreign frame is refused; a second delivery of the same bytes here (the paragraph on the first frame delivered a second time takes it); the responder's reply (its `encrypt`: two paragraphs below), the initiator's receipt of it (three paragraphs below) and any later message; the one-time path in an
exhibited run; the model's own `establishResponder` equality. The responder successor's `Session::invariant` and its four
counter ceilings are the next paragraph's.

*The responder's session after the first receipt.* `UnitLifecycleResponderSuccessor.lean` shows that the session the
successful call above returns passes `Session::invariant` and meets the four counter ceilings
(`initiator_first_send_responder_successor_admissible`, `initiator_first_send_responder_successor_counterHeadroom`,
`initiator_first_send_responder_successor_hypotheses`, with the relation; no compiler-trust axiom, as for the results above). **No law
and no premise about the run is added**: the statements take the hypotheses of `initiator_first_send_responder_receives`
(or `responder_first_frame_succeeds`) without the store bound `EstablishResponderHeadroom`, which the call's success
equation they add makes unnecessary. The invariant uses `DhPublicValid` and `OptionEqU64Shape`, already premises there, and
`DivCeilValue` and the header-length bound, both fields of the responder's contracts; the responder's oracle record and the
view's codec relation tie the drawn candidate's public key to the Triple's new sending key. It is proved for this one receive,
the first at the responder's prepared session, not through a theorem that a receive keeps the invariant, which the tree does
not have: from a walk of the successful `decrypt_ratchet` (what it writes), the relation of the section above (which fixes the
Triple's counters and stores and the agreement's state, by injectivity of the byte reading) and a walk of `Braid::receive` at
`NoHeaderReceived` (the relation does not fix the decoder: the decoder relation is behavioural). So the agreement's decoder is
shown to be the fresh header decoder or one `add_chunk` of it, which passes `Decoder::invariant`. The reach's run of the section
above meets both (`first_send_receive_successor_reachable`). **Not shown:** that a receive keeps the invariant in general or at
any later message; the reply (its `encrypt` is the next paragraph's); a second delivery of the same bytes here (the paragraph on the first frame delivered a second time takes it); the premises of the next decrypt that are not about the
session (the next frame's chunk relation, `HonestChunk` for the next header chunk, the draw, the boundary records); that the
model session the successor is related to holds only bytes the responder received (the relation is at the attributed view
above; the invariant and the ceilings are about the code's session and do not mention the view).

*The responder's reply.* `UnitLifecycleResponderReply.lean` takes the responder's public `Session::encrypt` at the session the
successful call above returns, on the same run (the same session, from the same call on the same bytes). At that session the
call has one outcome: it returns the bare reply frame (agreement type `none`, no chunk, no initial wrapper, sealed under the
key of the receipt's classical sending chain and the sparse chain the initiator receives on), takes no draw, returns the
session with only the Triple Ratchet replaced, and relates to the model's step (`initiator_first_send_responder_replies`;
with `responder_reply_refines`, the two derivations that keep the receipt's key equations and the reach
`first_send_reply_reachable`, it lists no compiler-trust axiom: the encrypt and decrypt refinements' nine `native_decide`
constants are kernel proofs since 2026-10-21). **No law and no
premise about the run is added.** The headline takes the hypotheses of `initiator_first_send_responder_successor_hypotheses`
and two boundary records at the responder's source, both of kinds the initiator's first send already takes: the full oracle
record `OracleOf` (in place of `DecryptOracleOf`) and the Braid send record `BraidSendRefinementContracts`. Like the
initiator's, they are assumed and not shown of the real primitives; the reach meets them with the run's own encrypt records
because there the two parties share the oracle and the byte-stream source type. The Braid send record carries the KEM
agreement `KemAgreesFor` at the responder oracle's KEM, as the generic route takes it for every state, although the
agreement's send at this state reads neither randomness nor the KEM; whether it could be dropped here is not checked. The
headline so takes `KemAgreesFor` at both parties' KEMs (the initiator's and the responder's Braid send records); each ties
its KEM to the same translated code, so the premises carry an indirect, weak relation between the two KEMs. The
source state is free, with no draw premise, and the plaintext bound `102 + (ptR.length + 48) ≤ Usize.max` holds of every plaintext of at most `2^32 - 151`
bytes on a 32-bit target. No refusal is possible at this state: the terminal guard is false, the agreement's send at
`NoHeaderReceived` does not refuse, and the model's Triple send from the receipt's Triple succeeds (counters 0, a sending
chain), so the statement has one outcome and not a refused arm; the refusals `encrypt` can reach elsewhere in a session (the
terminal guard, the Triple's `ChainExhausted` and `NoSendingChain`) are not covered. **Not shown:** the initiator's receipt of
the reply (the next paragraph); `Session::invariant` and the ceilings
after the reply are derived on this run in the send-preservation paragraph below; a second reply, the header's later chunks and the responder's first sampling send (a second message from
the initiator is taken, under a condition, in the second-send paragraph below); a restored copy of the session; that the model session the successor refines holds only bytes the responder
received (the relation is at the receipt's attributed view); that ML-KEM decapsulation agrees on a run (`FirstKemAgrees`);
`PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own `establishResponder` equality; the one-time path in a
run. The statement does not tie the source state to the one `establish_responder` left; it holds for every source state,
that one included, and the reach takes it.

*The initiator's receipt of the reply.* `UnitLifecycleResponderReplyReceipt.lean` takes the reply's bytes to the initiator, on
the same run: its public `Session::decrypt` at the session its own first `encrypt` left, from the source that `encrypt` left.
The call returns, takes exactly one draw, and is one of the four arms of the model's step: `Handshake(NonContributoryAgreement)`
(the initiator oracle refuses the agreement of its draw with the reply's ratchet key), `Triple(Classical(NoReceivingChain))`
(the reply's ratchet key is the peer key the initiator holds, so no Diffie-Hellman step is taken and it has no receiving chain),
`Aead` (the initiator's open of the responder's own seal refused, not a bad frame's refusal), each with the session as given, or
what the open returns, with the pending initial message cleared and the session related to the model's step
(`initiator_receives_reply_outcomes`). That is the general outcomes analysis. Under its own premises `DhAgreeContributory` and
`AeadRoundTrip` the `Handshake` and `Aead` arms do not occur, so the call refuses `NoReceivingChain` exactly when the reply's
ratchet key is the peer key and otherwise returns the responder's plaintext (`initiator_receives_reply_two_outcomes`, with no
added premise); with `hfreshB` added it returns the plaintext (`initiator_receives_reply`). The three, the reach run
`reply_receipt_reach_run` and the two reaches list no compiler-trust axiom (until 2026-10-21 they inherited the encrypt
and decrypt refinements' nine `native_decide` constants, kernel proofs since). **No new law is used by the three headlines**: they use the
receipt's `AeadRoundTrip`, `DhAgreeSymmetric` and `DhAgreeContributory` with the two oracles' roles swapped (the responder
seals, the initiator opens; the initiator's first agreement is the responder's `dSend` by symmetry; the initiator's draw agrees
with the reply's key by contributoriness), and `DhPublicValid` for the reply's ratchet key. They take two boundary records at
the initiator's source, of kinds the decrypt refinement already takes: `DecryptRatchetContracts` and `DecryptRatchetAgreements`
at the initiator oracle's KEM (which also gives the `KemLenAgrees` and `ValidateEkAgrees` that the invariant at the session
after the first send needs). Like the others, they are assumed and not shown of the real primitives; the reach meets them with
the responder contracts' decrypt record and the decrypt agreements, because there the two parties share the source type and the
oracle's KEM. At the initiator's `KeysSampled` agreement the translated `Braid::step_receive` returns the state it was given
unless the message is a `Ct1` chunk (by reading the generated code; no theorem states it), and the model's receive likewise, so the receipt runs no encapsulation, decapsulation or
key generation and needs no fact relating the two parties' KEMs (it does clone the key pair, under `KemCloneAgrees`);
`DecryptRatchetAgreements` still carries `KemAgreesFor` at the initiator oracle's KEM, as the generic route takes it for every
state, and whether it could be dropped here is not checked. One law, used only by a reach, and two premises about the run are
new:

| Statement | Kind | Says | Used for | Model, and when it would be false |
|---|---|---|---|---|
| `DhPublicNotConstant` | law, ASSUMED (`DhPublicNotConstantShape` at the real constants) | for every 32 bytes `pa` there are 32 bytes from which `from_bytes` makes a private key whose public key's bytes are not `pa` | the reach chooses the responder's 32-byte source so that its fresh ratchet key is not the signed prekey's (`first_send_reply_receipt_reachable`); no headline takes it | `InterpO.modelReply` (`modelReply_notConstant`): the base point and the key `1` are their own toy public keys, and they differ. False in `InterpO.modelFirstReceipt` (`modelFirstReceipt_not_notConstant`), whose public key is the base point for every key. True of X25519 by reading (`tacenta-core/boundary/src/dh.rs`: the public key is the base point multiplied by the clamped scalar, so two scalars `s`, `t` with `s ≢ ±t` modulo the group order give different public keys, and the public key takes more than one value); not checked in Lean. It would be false of a `public_key` that ignores its argument or of a `from_bytes` that maps every input to one key |
| initiator draw premise | premise about the run | the initiator's source after its first send holds a draw | the receipt's candidate draw (the refinement takes it); without it the model refuses `ceiling` | holds in the reach's run, whose initiator source is a 64-byte seed followed by 32 bytes. As for the responder's trace premise, a real `RngCore` does not run dry; the empty trace is a property of the trace interpretation |
| `hfreshB` | premise about the run, success theorem only | the responder oracle's public key of its draw is not the peer key the initiator holds (the bytes of the signed prekey) | the reply's ratchet key is fresh, so the initiator takes a Diffie-Hellman step and has a receiving chain | holds in the reach's run with the responder's source chosen by `DhPublicNotConstant`, and fails in `first_send_reply_stale_reachable`, whose responder draws its own signed prekey secret: there the initiator refuses `Triple(Classical(NoReceivingChain))` with its session unchanged. A condition on the run, not a law: it fails exactly when the responder's draw gives the signed prekey's public key. That it holds under an honest random source is not shown, and no probability is claimed |

The laws of the premise lists hold together, with the reach's `DhPublicNotConstant`, in `InterpO.modelReply`
(`reply_receipt_laws_model`, which proves every conjunct of `first_receipt_laws_model` again there): the first receipt's joint
model with a public key that is the private key when that key is canonical and not all zero and the base point otherwise, and
an agreement that refuses the all-zero key and otherwise returns the base point. A toy that shows nothing of the real
primitives: its agreement ignores the private key, so symmetry and contributoriness hold degenerately and every agreement
value is the same constant; it cannot tell which key sealed the reply, and that a non-degenerate symmetric agreement is
consistent with the other laws rests on reading X25519. It was needed because in `InterpO.modelFirstReceipt` every public key is the base point, so the responder's fresh
key always equals its signed prekey's and the initiator's receipt of the reply could only refuse. None of the new premises
mentions a platform width; the reply's plaintext bound is the reply paragraph's, and the reaches' plaintexts (every reply
plaintext of at most 4096 bytes; the initiator's first plaintext is empty) meet every bound at both widths. **Not shown:** that a tampered or foreign reply frame is refused (no AEAD authenticity law is assumed; a frame with the reply's header and a ciphertext that carries no tag is refused under an assumed law in the tampered-reply paragraph below); a second
message in either direction (a second reply, the header's third chunk, the responder's first sampling send; the
initiator's next send is the next paragraph, under a condition, and its step uses no fact relating the two parties'
Braid KEMs);
`Session::invariant` or the ceilings after the receipt of the reply (those after the reply are derived in the
send-preservation paragraph below, and those after its receipt in the receive-preservation paragraph after it); that the code's agreement after the
call equals the one before (it refines the same model agreement); that `hfreshB` holds under an honest random source; a
restored copy of either session; the one-time path in a run.

*The initiator's second send.* `UnitLifecycleInitiatorSecondSend.lean` takes the initiator's next `Session::encrypt`, on the
same run, at the session the receipt of the reply returns and from the source that receipt left. The model's step there has
one outcome: the bare second frame (agreement type `hdr` with the header's chunk at index 1, previous chain length 1,
message number 0 on the chain the receipt derived, sparse epoch 0 and number 2, no initial wrapper), no draw, the header
encoder advanced (`second_model_step`). The code-level part is **conditional**: if that session passes `Session::invariant`
and meets the four counter ceilings, the call returns those bytes, leaves its source as given and refines the step
(`initiator_second_send_after_reply`); neither premise is derived in that module, and no run is exhibited there at which
they hold, so there that part is not shown to apply to any run (the second-message paragraph below joins it with the
receive step that derives both premises, and exhibits such a run). The encrypt route's two Triple condition records are derived from the invariant and
the ceilings at every session whose model agreement send reads no draw (`encryptProviders_of_invariant`). The two composed
results list no compiler-trust axiom: the nine `native_decide` constants they used to inherit are kernel proofs since
2026-10-21. The headline's statement pin prints the statement without a cut (the module sets `pp.deepTerms true` and
`pp.proofs.withType true` before its pins; without them Lean cut it off with `⋯` after the binder `crcB`). It is not the
whole elaborated statement: Lean's printing leaves out, among other things, instance arguments, the function behind a coercion `↑`, implicit arguments, the binder types of `∃` and `fun`, universe levels, and the types behind numerals, anonymous constructors and structure instances. A
definition the statement names changed under the same name, a new instance in scope or a function given the `coe`
attribute can change what it means without changing the pin; `check-lean-constructs.sh`, a textual guard on the source, refuses in hand-written Lean an `instance` declaration whose whole text is not one of those it lists for that file and namespace (fifteen today: twelve `instance` and three `deriving instance` declarations), any attribute list naming `instance`, `default_instance` or `coe`, and the `coe` and `default_instance` tokens anywhere in code. A `deriving instance` needs no entry when each of its types is written as a name the file gives one of its own declarations; the names are compared as written, with no namespace resolution, so a type of another file written by a short name that the file also declares is accepted. It does not read a `deriving` clause of a `structure`, `inductive` or `def`, a class whose parent is a notation class, or a scoped instance of a dependency that an `open` brings into scope. That the pinned statement is the right one
is decided by reading. **No new law and no new per-run premise**: beyond
the receipt's hypotheses the headline takes only a bound on the second plaintext, `102 + (ptS.length + 48) ≤ Usize.max`,
which holds of every plaintext of at most `2^32 - 151` bytes on a 32-bit target, and it reuses the initiator's encrypt records
at the source the receipt left. At `KeysSampled` the translated `Braid::send` clones the state, advances the encoder and
returns the source as given (`braid_send_keysSampled`, hypothesis-free), so the step takes no draw and runs no
encapsulation, decapsulation or key generation, and no fact relating the two parties' KEMs is used for this step (the
receipt's premises it inherits carry `KemAgreesFor` at both parties' KEMs, as the reply paragraph records); the Braid send record
still carries `KemAgreesFor` at the initiator oracle's KEM, as the generic route takes it for every state, and whether it
could be dropped here is not checked. The relation after the call holds the cloned key pair through `KemCloneAgrees`;
code-level equality of the key pair is not checked. **Not shown:** `Session::invariant` or the ceilings at the session the
receipt returns (the receive-preservation paragraph below derives them there, and the second-message paragraph below
joins that with this send; this module does neither) or after the second send; the responder's receipt of the second frame (shown, on the same run, in the paragraph on that receipt below), a second reply and its receipt, the
header's third chunk, the responder's first sampling send and every later step, so no second exchange; a refusal `encrypt`
can reach (none occurs at this state; the terminal guard, `AgreementFailed`, `ChainExhausted` and `NoSendingChain` elsewhere
are not covered); a restored copy of the session; the one-time path in a run; that the related model sessions hold only
bytes the parties received; that `hfreshB` holds under an honest random source; that the real primitives meet the records
or the laws; `FirstKemAgrees`; `PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own `establishResponder`
equality.

*The initiator's refusal of a tampered reply.* `UnitLifecycleTamperedReply.lean` takes, on the same run as the receipt of
the reply, every frame that keeps the reply's first 102 bytes (its header) and carries other bytes in place of its
ciphertext, and shows that the initiator's `decrypt` at the session its first `encrypt` left, from the source that
`encrypt` left, refuses it with `Aead`, returns the session as it was and takes exactly the one draw the honest receipt takes
(`initiator_refuses_tampered_reply`, resting on the kernel and opaque constants, no compiler-trust axiom). It needs one new
assumed law and one new premise about the run, on top of the reply receipt's premises (`hfreshB` included), and, like every
encrypt result, it is conditional on the seal's totality contract `AeadSealBounded`, which is stated for every length and false of the shipping seal by reading, from a plaintext of `2^30 - 16` bytes on a 32-bit target and `2^62 - 16` on 64-bit (the totality row below, which says what that means for every result that takes it), and on the open clause of the oracle record `OracleOf` (it asks the boundary's `decrypt` to return on every input, and so implies `AeadOpenTotal`), which the refusal uses at the tampered ciphertext's length; `AeadOpenTotal` is false, by reading, from about `2^61` bytes of associated data and ciphertext on a 64-bit target built with overflow checks (the same row). As stated, the result therefore says nothing about the shipping code at any length (the same row):

| Statement | Kind | Says | Used for | Model, and when it would be false |
|---|---|---|---|---|
| `AeadOpenChecksTag` | law, ASSUMED (`AeadOpenChecksTagShape` at the real constants) | if `aead::decrypt` of `c` under keys, IV and associated data `ad` returns `Ok`, the last 32 bytes of `c` are `Model.Kdf.hmac` under the MAC key over `ad` and the bytes before them | the oracle's open of bytes that carry no such tag is refused (`open_none_of_not_tagged`), so the model's step refuses `aead`; with `AeadRoundTrip`, the reply's own ciphertext carries it (`not_notTagged_of_seal`) | `Interp.modelTagged`, whose toy seal appends the model's HMAC tag and whose open checks it (`tamper_laws_model`); not implied by `AeadRoundTrip` (`taggedLenient_roundTrip_not_checksTag`); false of a truncated or short-circuit comparison, a tag over other bytes or an open that accepts on another condition; it names no seal and no length, and survives a seal that fails at long lengths (`taggedTop_checksTag_not_openSealUnique`; the toy fails past `isize::MAX`, the shipping seal from about half of that) |
| `NotTagged` | premise about the run, crypto-bearing | the frame's replaced bytes do not carry that tag under the reply's MAC key and associated data | the tampered frame's open is refused | a condition on bytes, the same at every interpretation; met by every ciphertext shorter than 32 bytes, at the real constants included (`notTagged_of_short`); false of every body followed by its tag (`tagMatches_append`) and of the reply's own ciphertext (a conjunct of the headline); that an attacker without the message key cannot produce, except with negligible probability, bytes that carry the tag is the unforgeability of HMAC-SHA256, which no theorem states and none can prove of the real function; width-free |

**The law is not realised against the shipping AEAD.** By reading, `tacenta-core/boundary/src/aead.rs` refuses an
input shorter than 32 bytes, streams the associated data and then the ciphertext into RustCrypto `Hmac<Sha256>`
(`hmac` 0.12.1, `sha2` 0.10.9) under the 32-byte MAC key, and returns a plaintext only after `verify_slice` accepted
the full 32-byte tag. So an accepted input carries the HMAC-SHA256 tag over `ad ‖ ciphertext`. That RustCrypto's
HMAC computes `Model.Kdf.hmac` is not proved. `Model.Kdf.hmac` is anchored to RFC 4231 by `native_decide` examples
in `tacenta-model` and by the HMAC vectors. Nothing about AES, CBC or the padding enters this law.

The workspace builds with overflow checks on (`[profile.release]` in `tacenta-core/Cargo.toml`, for every crate but
`subtle`), and `sha2` 0.10.9 computes the message's bit length as `8 * (bytes hashed)` in a `u64`, so from about `2^61`
bytes of associated data and ciphertext (64-bit only) the open's SHA-256 length arithmetic would panic (by reading of
`sha2`'s source, not tested). There the open does not return, and the law holds, but `AeadOpenTotal` does not; the
totality row below records that edge, and the tampered-reply refusal takes the open clause of the oracle record `OracleOf` (it asks the boundary's `decrypt` to return on every input, and so implies `AeadOpenTotal`) at the tampered ciphertext's length, so it is conditional on it there. That falsity depends on the build profile, since an application that depends on `tacenta-core` builds it with its own: with overflow checks off, `sha2` wraps the bit length and the open returns. The law does not depend on the profile: `Model.Sha256.pad` takes `UInt64.ofNat len * 8`, which wraps exactly as `sha2` does, so past `2^61` bytes, where FIPS 180-4 no longer defines SHA-256, the open either panics or computes `Model.Kdf.hmac` (by reading).

A realisation would need the shipping open translated, with its tag computed by a translated HMAC. An independent
verified implementation of the same construction proves this shape of its own `decrypt` (a bad tag refused, for
every input); that is about another implementation, and adopting it is an owner decision this work does not make.
The earlier law, `AeadOpenSealUnique`, is no longer assumed. It said an opened ciphertext reseals to itself, which is
false of the shipping functions wherever the reseal cannot return: the seal's `mac` copies `ad ‖ ct` into one `Vec`,
which panics past `isize::MAX` bytes and aborts under memory exhaustion, and before that the seal's tag append panics from a padded ciphertext of half of `isize::MAX` (the totality row), while the open does not allocate either. The law
therefore stays a reviewed external assumption, and the premise stays a condition on the run.

**Not shown:** that the shipping AEAD meets the law; that a frame an attacker can produce meets the premise; a frame
whose tag verifies but whose padding is refused; `AeadSealBounded` at the reply's plaintext from about half of `isize::MAX` (the
totality row); `AeadOpenTotal` at a tampered ciphertext from about `2^61` bytes on 64-bit with overflow checks (the totality row); a frame whose header bytes were changed, a frame
shorter than the header or of another type; the refusal when the reply's ratchet key is the peer key or the draw's agreement
is refused; that the refusal's source equals the honest receipt's; a run in which the honest reply is received after a
refused tampered frame; tamper refusal on any other route; redelivery of the honest reply, here (its delivery a second
time after the first receipt is the paragraph on the reply delivered a second time). The statement pin of
`initiator_refuses_tampered_reply` prints the whole statement, the law (its first hypothesis) included (the module sets
the two `pp` options before its pins), which is still not the whole elaborated statement: what Lean's printing leaves out
is held by the build and by reading only, as for every statement pin.

**Send preservation where the agreement's send takes no draw** (`UnitTripleInvModel.lean`, `UnitLifecycleSendPreserve.lean`).
The bridge (`triple_invariant_iff_model`) rests on the kernel alone and assumes nothing beyond the Triple relation. The
general step (`encrypt_keeps_invariant_no_draw`) rests on the kernel and opaque constants and assumes the boundary record
`KemCloneAgrees` (ASSUMED, a field of `BraidSendRefinementContracts`: a key pair's clone answers `header`, `ek_vector` and
`decapsulate` as the original did, and an encapsulation state's clone answers `encapsulate2`; this step uses the first
two) and takes the relation after the call as a hypothesis. That relation carries the Triple half (the code Triple's
invariant is read off the model Triple it relates to), the three Triple fields the structural clauses read and the
budget; only the agreement half is a walk of translated code, and the code's Triple send is never walked. Every instance
gets the relation from the encrypt refinement, which rests on the kernel and opaque constants since its nine
`native_decide` constants became kernel proofs on 2026-10-21, so the run results list no compiler-trust axiom either.
The statement pins of the two run headlines, `initiator_first_send_responder_reply_successor` and
`initiator_first_send_responder_reply_admissible`, print their statements without a cut, through the conclusion (the
invariant, `CounterHeadroom`, `CounterRoom` and the relation; without the module's `pp.deepTerms` and `pp.proofs.withType`
options Lean cut both off with `⋯` after `AeadRoundTrip →`). They are not the whole elaborated statements: Lean leaves out,
among other things, instance arguments, coercion functions, implicit arguments, the binder types of `∃` and `fun`,
universe levels and the types behind numerals and structure instances, so a definition the
statements name changed under the same name, a new instance or a `coe` function can change their meaning without
changing the pins, and that they are the right statements is decided by reading.
Its statement covers the nine agreement
states whose send takes no draw; its premises, that relation and the agreement walk's included, are exhibited together
only at `NoHeaderReceived`, on the reply's run, and at the other eight states no run here exhibits them (the relation after
the call there would come from an encrypt refinement whose leaf hypotheses are not discharged at those states). It does
not cover `KeysUnsampled` or `HeaderReceived`, whose sends draw and (at `HeaderReceived`) hand the Triple an
agreement output; a Triple send with an output (`advance`, a new chain pair, `clearOldEpochs`) is not covered. **The
ceilings are a budget, not preserved.** The refinement theorems ask for one step below each ceiling (`CounterHeadroom`),
and by reading the code refuses one step later: the ratchet's clock clamps at `u32::MAX - 1` and never refuses
(`tacenta-core/ratchet/src/lib.rs`, `age_store`), a sparse chain counter steps to `u64::MAX` (the send after it refuses,
`ChainExhausted`), and the sparse epoch and the Braid epoch (transitions (5) and (13)) reach `u64::MAX - 1`. So a session
whose sending chain is at `u64::MAX - 1` meets `CounterHeadroom`, a send from it succeeds, and the session it leaves does
not meet it: "an operation keeps the ceilings or refuses" is false of the code. The statements spend `CounterRoom s k`
instead, room for `k` more operations, each costing at most one step of the clock and of each epoch and at most
`MAX_SKIP + 1` of a chain counter; `CounterRoom s 0` is `CounterHeadroom s` (`counterRoom_zero`). `CounterRoom` is a
per-run budget: it excludes runs longer than its `k` and the parked clock, and asks nothing else of a state. It is in `u32` and `u64` only, so it means the same at both widths. The run's headline computes it
at the responder's session after the first receipt (clock 1, so room for every `j` with `j + 2 < u32::MAX`) and concludes
`CounterHeadroom` after the reply; the budget at any other session is not computed. The weights are for operations in general;
nothing here covers a receive (an in-order receive at two agreement states stays within them, the next paragraph;
whether any other receive does is not checked). **Not shown:** `encrypt` at
a state whose send draws; the session a refused `encrypt` returns; any receive keeping the invariant; that the real key pair
meets `KemCloneAgrees`; that `Session::invariant` says a session is reachable.

**Receive preservation on an in-order receive** (`UnitLifecycleReceivePreserve.lean`). The general step
(`decrypt_ratchet_keeps_invariant_in_order`, and `decrypt_keeps_invariant_in_order` for the public call) rests on the
kernel and opaque constants and assumes the boundary record `KemCloneAgrees` (ASSUMED, as for the send; this step uses the
key pair's clone answering `header` and `ek_vector`), the decrypt oracle record's `dhPublic` clause and the view's codec
relation `DhCodecOf` (ASSUMED records: the public key the boundary computes for a private key is the oracle's), and the law
`DhPublicValid` (ASSUMED, the establishment's: a public key's bytes are canonical); it takes the relation after the call
and the model step as hypotheses. That relation carries the Triple half (the code Triple's invariant is read off the model
Triple it relates to), the direction, the sparse epoch and the budget; only the agreement half and clause (a) are read off
translated code (the walk of `Braid::receive` and the call's own walk of the new ratchet key), and the code's Triple
receive is never walked. Every instance gets the relation from the decrypt refinement, so the two run results list no
compiler-trust axiom either. **Its scope is narrow.** The model step must be an `InOrderReceiveStep`: no stored key used in
either ratchet, no message skipped on either chain (so no store entry is written and no eviction runs), no agreement
output, and the agreement kept at `NoHeaderReceived` or at `KeysSampled` at the same epoch; at `NoHeaderReceived` the
decoder holds at most one chunk before the call. The decoder lemmas cover at most two chunks after the call: a general proof
that `add_chunk` keeps `Decoder::invariant` (the bitset loop of `Decoder::invariant` at any length) was judged a separate
piece of work and not attempted, and the two-chunk form is enough for the responder's receipt of a second message, which
the paragraph on that receipt below applies it to (this module does not). Its premises are exhibited together at `KeysSampled` on the reply's run
(`initiator_receives_reply_successor`, which gives `Session::invariant`, `CounterHeadroom` and room for every `j` with
`j + 2 < u32::MAX` at the session the initiator's receipt of the reply returns) and at `NoHeaderReceived` with an empty
decoder on the first frame's run (`responder_successor_via_preservation`, which re-derives the conclusion of
`responder_first_frame_successor` from the prepared session's invariant with no shape of the session after the call); no
run here exhibits them at a decoder holding one chunk. The statement pins of those two run results print the whole
statement (the module sets the two `pp` options before its pins), which is still not the whole elaborated statement: what
Lean's printing leaves out is held by the build and by reading only, as for every statement pin. **The budget.** An in-order receive
moves the clock by at most one (it clamps at `u32::MAX - 1`), keeps both epochs, and steps one sparse receiving chain by
one, within the weights of `CounterRoom`; the budget is computed at the initiator's session after its first send (room for
`j + 1` operations whenever `j + 2 < u32::MAX`) and at the responder's prepared session (room for one), and at no other
session. **Not shown:** a receive that uses a stored key, skips, or evicts, so reordered, delayed or dropped delivery; a
receive with an agreement output or one that moves the agreement to another state (the header completing, a `ct1` chunk),
or at any other agreement state; a decoder holding more than one chunk before the call; the session a refused
`decrypt` returns; that the relation after the call holds or that the model's step is in order (hypotheses, supplied on the
two runs); the initiator's second send composed with the invariant at the session its receipt returns (the second-send
paragraph above states its code-level part under that condition; the next paragraph joins the two, this module does
not); any later message; a restored
copy of a session; that the real primitives meet the records and laws; that `Session::invariant` says a session is
reachable.

**The initiator's second message** (`UnitLifecycleInitiatorSecondMessage.lean`). `initiator_sends_second_message`
joins the second send with the receive step on one run, under exactly the hypotheses of `initiator_second_send_after_reply`
(those of `initiator_receives_reply` and the bound on the second plaintext): the session the initiator's receipt of the
reply returns passes `Session::invariant` and meets the four ceilings (from `initiator_receives_reply_successor`), so the
second `encrypt` there returns the bare second frame, takes no draw and refines the model's step with no condition, and
the session it leaves passes `Session::invariant`, meets the ceilings and has room for every `j` with `j + 3 < u32::MAX`
(`encrypt_keeps_invariant_no_draw` at `KeysSampled`). The two composed theorems name their sessions separately; they are
identified because both state the same two calls on the same inputs and the calls are functions. It adds no law and no
per-run premise; the preservation step's record `KemCloneAgrees` (ASSUMED, as above) comes from the initiator's Braid send
record. `first_send_second_message_reachable` exhibits, at the real constants under the laws of
`first_send_reply_receipt_reachable` (all ASSUMED, `DhPublicNotConstant` included), a run at which every hypothesis of the
headline holds; its conclusion is the definition `SecondMessageRun`. Both rest on the kernel and opaque constants with no
compiler-trust axiom. The headline's statement pin, the reach's pin and the `#print` pin of `SecondMessageRun` print
the whole statement (the module sets the two `pp` options before its pins), which is still not the whole elaborated
statement: what Lean's printing leaves out is held by the build and by reading only, as for every statement pin. **The budget** after the send is what the
composition derives, not the exact room: the preservation step charges a unit for the send although the clock does not
move. **Not shown:** the responder's receipt of the second message (shown, on the same run, in the next paragraph), a
second reply and its receipt, the header's third chunk, the responder's first sampling send and every later step, so no second exchange; a refusal `encrypt` can reach
(none at this state; those reachable elsewhere are not covered); code-level equality of the key pair before and after the
call; the reply's bytes as `replyFrame` and the frame equation of the receipt's session against the session before it (not
carried); a restored copy of either session; the one-time path in a run; that the related model sessions hold only bytes
the parties received; that `hfreshB` holds under an honest random source; that the real primitives meet the records or the
laws; `FirstKemAgrees`; `PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own `establishResponder` equality;
that `Session::invariant` says a session is reachable.

**The responder's receipt of the second message** (`UnitLifecycleResponderSecondReceipt.lean`).
`responder_receives_second_message_two_outcomes` takes the initiator's second frame, on the run of
`initiator_sends_second_message`, to the responder's public `decrypt` at its session after the reply, from the source the
reply left, under that theorem's hypotheses and the per-run premise that this source holds a draw: the call either
refuses `OutOfOrder` with the session unchanged, exactly when the initiator's new ratchet key is its first ratchet key, or
returns the second plaintext and a session related to the model's step. `responder_receives_second_message` adds the
per-run premise that the new key is not the first, and carries `Session::invariant`, the four ceilings and a budget
through the receive by the in-order receive step above, at `NoHeaderReceived` with one chunk held (a walk of
`establish_responder` shows its session holds at most one; the reply keeps the agreement). No new law; the records and laws
are the run's (ASSUMED, as above), `DhAgreeSymmetric` giving the responder's first agreement from the initiator's. The
second chunk does not complete the 96-byte header, so the model's step runs no KEM operation and no header check (the
code's, by reading the generated code), and no fact relating the two parties' Braid KEMs is used by this step (the run's premises still include `FirstKemAgrees`,
about the prekey encapsulation of the first message). The two per-run premises are conditions on the run, not laws: the draw and the
initiator's new key, both from the random sources; no probability is claimed. `first_send_second_receipt_reachable` and
`first_send_second_receipt_stale_reachable` exhibit, at the real constants under the laws of
`first_send_second_message_reachable` (all ASSUMED), a run that returns the plaintext with the invariant and the ceilings
after it, and one that refuses (the initiator's 32 further bytes those of its first ratchet key). All rest on the kernel and
opaque constants with no compiler-trust axiom. The statement pins of the two headlines, of the run and of the reaches, and the `#print` pins of the runs, print
the whole statement (the module sets the two `pp` options before its pins), which is still not the whole elaborated
statement: what Lean's printing leaves out is held by the build and by reading only, as for every statement pin. Of the
success headline's conclusion only the four calls, the plaintext equation and the invariant and ceilings after the
receive are consumed by a later proof; its other conjuncts are pinned and used by no later proof. **The budget** after
the receive (room for every `j` with `j + 3 < u32::MAX`) is what the composition derives; by reading it is exact there (the
clock is 2), and exactness also follows from the headline's relation conjunct, which no theorem here states. **Not shown:** a second reply (shown, on the same run, in the next paragraph) and its receipt, the header's third chunk, the responder's first sampling send
and every later step, among them the responder's check of the completed encapsulation key, the first step at which both
parties' KEMs act on one key pair; a tampered, foreign or replayed second frame's refusal (no AEAD authenticity law); a
receive out of order, with a stored or skipped key, or with more than one chunk held before it; code-level equality of the
agreement or key pair before and after the call; a restored copy of either session; the one-time path in a run; that the
related model sessions hold only bytes the parties received; that the per-run premises hold under honest random sources;
that the real primitives meet the records or the laws; `FirstKemAgrees`; `PrekeyIdsDistinct` from
`PrekeyStore::invariant`; the model's own `establishResponder` equality; that `Session::invariant` says a session is
reachable.

**The responder's second reply** (`UnitLifecycleResponderSecondSend.lean`). `responder_sends_second_reply` takes the
responder's next operation on the run of `responder_receives_second_message`, under exactly that theorem's hypotheses
(its two per-run premises, the responder's draw after the reply and `hfreshA`, included) and a bound on the plaintext
`ptR2`: the public `encrypt` at the session the receipt returns, from the source the receipt left, returns the bare second
reply frame, takes no draw, writes only the Triple Ratchet and refines the model's step, and the session it leaves passes
`Session::invariant` (`encrypt_keeps_invariant_no_draw` at `NoHeaderReceived`, from the invariant and one unit of the
budget the receipt leaves) and meets the four ceilings. The encrypt route's providers come from the invariant and the
ceilings at the receipt's session (`encryptProviders_of_invariant`). No new law and no new per-run
premise; the records are the reply's at the responder's source (ASSUMED, as above), `KemCloneAgrees` from its
`DecryptRatchetAgreements`. The agreement's send at `NoHeaderReceived` takes no draw (`braid_send_noHeader`) and, by reading the
walk of the translated send and the Rust, runs no KEM operation, and no fact relating the two parties' Braid KEMs is used by this step; the Braid send record
still carries `KemAgreesFor` at the responder oracle's KEM, as the generic route takes it for every state (whether it could
be dropped here is not checked). `first_send_second_reply_reachable` exhibits, at the real constants under the laws of
`first_send_second_receipt_reachable` (all ASSUMED), a run at which every hypothesis holds; its conclusion is the
definition `SecondReplyRun`. The encrypt there has one outcome, so no second arm is reached. All rest on the kernel and
opaque constants with no compiler-trust axiom. Every statement pin and the `#print` pins of the five definitions print the
whole statement (the module sets the two `pp` options before its pins), which is still not the whole elaborated
statement: what Lean's printing leaves out is held by the build and by reading only, as for every statement pin. Of the
headline's conclusion only the five calls, the two plaintext equations, the frame equation of the session after the send
and its invariant and ceilings are consumed by a later proof; its other conjuncts are pinned and used by no later proof.
**The budget** after the send (room for every `j` with `j + 3 < u32::MAX`) is read off the model session after the step:
the send does not advance the clock, which is 2 there; more room is not claimed. **Not shown:** the initiator's `decrypt`
of the second reply and every later step, among them the header's third chunk, the responder's first sampling send and
the responder's check of the completed encapsulation key, the first step at which both parties' KEMs act on one key pair;
a refusal `encrypt` can reach (none at this state; those reachable elsewhere are not covered); a tampered, foreign or
replayed frame's refusal on this route; delivery out of order, a stored or skipped key, or more than one chunk held before
a receive; a restored copy of either session; the one-time path in a run; that the related model sessions hold only
bytes the parties received; that the per-run premises hold under honest random sources; that the real primitives meet
the records or the laws; `FirstKemAgrees`; `PrekeyIdsDistinct` from `PrekeyStore::invariant`; the model's own
`establishResponder` equality; that `Session::invariant` says a session is reachable.

**The first frame delivered a second time** (`Translation/UnitLifecycleResponderRepeatedFrame.lean`,
`Translation/UnitLifecycleResponderEstablishReplay.lean`). On the run of the initiator's first send, the same bytes
delivered again to the responder are refused in both places they can arrive, with no durable effect.
`initiator_first_send_responder_repeat_refused`: at the session the first successful `establish_responder` returned, the
public `Session::decrypt` recognises the repeat, its inner receive refuses the frame as out of order
(`Triple(Classical(OutOfOrder))`), and it returns that session unchanged, refining the model's step; it takes one draw from
the source, the candidate key the inner receive draws before the Triple's receive, as the model's step does, so "no effect"
holds of the session and not of the random source. It rests on the kernel and opaque constants and on the first receipt's
laws (`AeadRoundTrip`, `DhAgreeContributory`, `DhAgreeSymmetric`, `DhPublicValid`, ASSUMED), with one per-run premise, that
the second source holds a draw; `DhAgreeContributory` also carries the repeat recognition's two agreements and the second
draw's, without which the refusal would be `handshake nonContributoryAgreement` instead. Its two statement pins
(`responder_first_frame_repeat_refused`, `initiator_first_send_responder_repeat_refused`) print the whole statement (the
module sets the two `pp` options before its pins), which is still not the whole elaborated statement: what Lean's printing
leaves out is held by the build and by reading only, as for every statement pin. `initiator_first_send_responder_replay_refused`: at the store the first success committed, `establish_responder`
on the same bytes returns `ReplayedLastResort`, that store and the source as given, when the bundle names the store's
last-resort KEM key and no one-time curve prekey (two premises on the run's shape, exhibited on the reach run); it takes
none of the receipt's laws, only the decoding facts `DhPublicValid` and `ZeroizingArrayRoundTrip` (ASSUMED), and the first
call's success as a hypothesis. It is a statement about the translated code alone: no relation between the code's prekey
store and the model's exists in the tree, so that the model's `establishResponder` refuses the same delivery is not shown.
Its statement pin prints the whole statement, with the same proviso. **Not shown:** a repeat at
any later session (after the responder's reply, after the initiator's second message, on a restored copy) or of the reply
at the initiator (the next paragraph takes the reply's, right after the first receipt); a repeat that differs in its bytes; the one-time path, whose second delivery the code refuses by reading
because the commit removed the key; a second delivery after a refused first call or after another store change; that the
replay record keeps the entry for the store's life.

**The reply delivered a second time** (`Translation/UnitLifecycleInitiatorRepeatedReply.lean`). On the run of the
initiator's first send, the responder's receipt and its reply, the reply's bytes delivered again to the initiator, at the
session `s''` its first receipt of them returned, are refused with no durable effect on the session.
`initiator_repeated_reply_refused`: the public `Session::decrypt` passes the bare frame to its inner receive, which
refuses it as out of order (`Triple(Classical(OutOfOrder))`: the reply's ratchet key is now the peer key held, no stored
key matches and message 0 is below the receive count 1), and it returns `s''` itself, refining the model's step; `s''`
passes `Session::invariant` and meets the four ceilings (from `initiator_receives_reply_successor` on the same run), so the
session after the refusal does too. It takes one draw from the source, the candidate key drawn before the Triple's receive,
as the model's step does, so "no effect" holds of the session and not of the random source. It rests on the kernel and
opaque constants and on the hypotheses of `initiator_receives_reply` (the receipt's laws `AeadRoundTrip`,
`DhAgreeContributory`, `DhAgreeSymmetric`, `DhPublicValid`, and the other laws and records named there, ASSUMED, with the
per-run premise `hfreshB`), with one per-run premise more, that the second source holds a draw; `DhAgreeContributory` also
carries the agreements of `s''`'s ratchet key and of the second draw with the reply's key, without which the refusal would
be `handshake nonContributoryAgreement` instead. The general step `reply_again_refused_of_invariant` takes the invariant,
`CounterHeadroom` and the relation to `replyReceiptSession` as hypotheses; on the run they are derived. The statement pins
print the whole statement, which is still not the whole elaborated statement, as for every statement pin. **Not shown:** a
delivery of the reply again at any other point (after the initiator's second send, after the responder's second message, on
a restored copy, or after a first receipt that refused, where `hfreshB` fails); a frame that differs from the reply in its
bytes on the run (a tampered reply at `s''`; the general step covers a frame that keeps the reply's header
and changes its ciphertext, but no statement takes one on the run) and any other out-of-order delivery (a later message
of the same chain arriving first,
delay or loss, a receive that uses a stored skipped key); the arms an empty source or a refused agreement would give; that a
refused call keeps `Session::invariant` in general (here the session returned is `s''` itself); every step that runs a KEM.

**What is not shown.**

- That the real primitives, or the real standard-library and `zeroize` functions, satisfy any field or any law. The
  model is a model of the shapes (most types are `Unit`, and most functions return a default). It implements
  `Vec::pop`, `Vec::truncate`, `usize::div_ceil`, `Option::as_mut` and `Vec::capacity` as the real operations. The
  blanket `Zeroize`, `Array::zeroize`, `Vec::zeroize` and the tuple `Zeroize` are the identity, which is not what they do.
- That the substitution step is sound inside Lean (above).
- That the headroom records are met by a state the crate can reach, apart from a session `establish_initiator_for` returns
  (and the encrypt record there, `encryptHeadroom_established`; the session its first successful `encrypt` leaves passes
  `Session::invariant`, above, so the receive record holds there by `decryptHeadroom_of_invariant` under `DhCodecTotal` and
  `Ct1LenTotal`, not stated as a theorem),
  and the session `establish_responder` builds before its inner receive (`counterHeadroom_responder_prepared`; that is not
  the session the call returns; the first receipt's reach, `first_send_receive_reachable`, exhibits one input at which the whole
  call succeeds).
  The witness session has no pending initial message and no established ephemeral key, and it is not one that
  `establish_initiator` or `establish_responder` returns. A session `establish_initiator_for` returns holds a pending initial
  message and passes `Session::invariant` under `KemCiphertextLenOf` and `DhPublicValid` (above), so
  `decryptHeadroom_of_invariant` gives it `DecryptRatchetHeadroom` under `DhCodecTotal` and `Ct1LenTotal`; the one state
  `establish_responder` returns that is shown to pass the invariant is the session it returns on the initiator's first frame
  (the responder successor paragraph above; the session it hands to its inner `decrypt_ratchet` passes it too,
  `responder_prepared_invariant`, above), and the encrypt record holds there (`encryptHeadroom_reply`, the reply paragraph
  above). No theorem shows that a `PrekeyStore` passes `PrekeyStore::invariant`
  or that the invariant bounds `last_resort_seen`, so `EstablishResponderHeadroom` is shown only as a bound on a vector length,
  with a key pair (`HeadroomInhabitants`) as a value. The Braid in the witness is in `KeysUnsampled`,
  which holds no decoder, ciphertext or KEM value; for the other states the receive record holds of every state that passes
  the invariant (`decryptHeadroom_of_invariant`), and no state in which the five KEM-state arms of `ct1_bounded` bind is exhibited.
- That a send or a receive keeps `State.decoders_bounded` and `State.ct1_bounded` at the level of the session. The
  Braid's own operations keep `State.sized`, which gives them (the subsection "The Braid's preservation
  theorems", below), but the lifecycle theorems are single-step, and nothing shows that a session state a
  theorem produces holds a Braid that its own operations reached.
- That the bounded `DecoderMessageTotal` is a statement about the real decoder. It is true of the translation:
  `Vec::with_capacity` never fails in the Aeneas model, and the real function panics for an absurd capacity,
  which `Decoder::invariant` excludes for a decoder a Braid holds.
- That the real `Array::zeroize` and `Vec::zeroize` return at the instances three fields are stated at (next paragraph).
- The classification of the fields (which are about opaque constants, which about translated functions) is
  checked by the audit text in `tacenta-proofs/scripts/check-session-satisfiability-negatives.sh`, which that script
  appends to a copy of the joint module and runs, and not by `lake build`.

**Three fields are stated at the unit's instances.** `SessionUnitSpqrT1.ZeroizeTotal`,
`SessionUnitBraidT1.ArrayZeroizeTotal` and the `Vec::zeroize` conjunct of `SessionUnitSpqrT1.VecRetainTotal` used to say
that `Array::zeroize` and `Vec::zeroize` return for every instance record `inst : Zeroize Z`, including one whose
`zeroize` fails. The real functions call `inst.zeroize` on each element and so fail on a failing instance: the general
forms were consistent (the joint model satisfied them) but stronger than the crate supports
(`UnitSatisfiabilityZeroizeScope.zeroize_failure_propagation_conflicts` and its two siblings, kept as the record). The
fields are now stated at the instances the unit passes: `Array::zeroize` at the blanket `u8` instance on a 32-byte
array, and `Vec::zeroize` at the chain table (`Vec<(u64, Chains)>`), the sparse skipped-key store (`Vec<Skipped>`) and
the classical one (`Vec<SkippedKey>`). A walk of the elaborated definitions of `TacentaSessionUnit.lean` found 34 calls of
`Array::zeroize`, all at that instance and width, and 5 of `Vec::zeroize`, at those three instances (2, 2 and 1). The walk
was run once, when the fields were restated; no gate repeats it. A new call at another instance or width in a function a
theorem steps through is expected to stop that proof, because the restated fields and their stepping rules apply at the
stated instance only (not checked); a new call in a function no theorem covers, such as a `Drop` implementation, would
go unnoticed. No proof steps through a call at the classical `Vec<SkippedKey>` instance; the conjunct is stated so that
the field covers every instance the unit passes, and the derivation of the sparse agreements passes it on only to build
`VecRetainTotal`.

What changed, and where. The Session copies are generated: the restated statements and the proof edits that use them
are named, count-checked `unit_edit`s in `port-session-unit-proofs.sh` (`SessionUnitSpqrT1`, `SessionUnitSpqrT3`,
`SessionUnitTripleT1`, `SessionUnitTripleT3`) and `port-session-braid-proof.sh` (`SessionUnitBraidT1`): eleven
applications of `ZeroizeTotal` drop the instance argument, three drop the instance placeholder (`hzs _ a` becomes `hzs a`), four uses of the
`Vec::zeroize` conjunct select the instance by projection, and `zeroize_step` and `array_zeroize_spec` are stated at the
one instance. One non-generated proof file, `UnitLifecycleTripleRefusalT3.lean`, needed the same two kinds of edit.
The standalone leaf files and the three-leaf unit keep the general forms, which are stronger than their crates in the
same way (`CLAIMS.md`, the section on hypotheses about translated functions in the leaf crates and the three-leaf
unit). The joint model gains one interpreted constant, the pair `Zeroize` (`Pair.Insts.ZeroizeZeroize.zeroize`), which
the chain table's instance reaches, and rebuilds the three instance records over the interpretation; the classification
audit allows the eleven structure accessors those records read, each only if the environment says it is a projection.
The statements of the three fields are pinned by `#print` (`UnitSatisfiabilityZeroizeScope.lean`).

What is assumed. That the real `Array::zeroize` returns at the blanket `u8` instance on a 32-byte array, and that the
real `Vec::zeroize` returns at the three instances. By reading, the blanket `Zeroize` writes zeros through volatile
stores, the element `zeroize` of the three instances reaches only that, `Array::zeroize` over it, the pair `Zeroize` and
`Option::as_mut`, and `Vec::zeroize` zeroizes each
element, clears the vector, which drops each element (`SkippedKey`, `Skipped`, `Chain` and `Chains` derive `ZeroizeOnDrop`, so each drop zeroizes
again), and zeroes its spare capacity; none of these returns an error or panics short of the memory
faults no proof here covers. This is not checked by a proof or a test. Every axiom-level shape, the restated fields among them, holds in an interpretation whose
`Array::zeroize`, `Vec::zeroize` and pair `Zeroize` work element by element and propagate a failure
(`faithful_satisfies_all_axiom_shapes`); that is a model of the shapes and says nothing of the real functions.

### The clauses of `OracleOf`: inhabited under eleven laws, and what that means

`OracleOf` (`UnitLifecycleT3.lean`) is the record the dispatch theorems take to tie the model's lifecycle oracle to the
translated primitives. `UnitOracleJoint.lean` shows it inhabited as a whole (`oracleOf_of_laws`) and adds a stronger
record, `OracleOfGuarded`, whose KEM success clause is guarded by the oracle's `kemValid` and not by its prediction
(`oracleOfGuarded_of_laws`). Both are theorems at the real constants under eleven laws, `OracleLaws`
(`oracleLaws_real_iff`), which are sufficient and not shown necessary:

| Law | Statement | Status |
|---|---|---|
| `DhCodecTotal`, `DhAgreeTotal`, `DhIdentityTotal`, `AeadSealBounded`, `AeadOpenTotal`, `KemDecapsulateTotal`, `XeddsaVerifyTotal` | the primitive returns on every input a Rust program can supply and memory allows; the Lean slice type admits lengths up to `Usize.max`, which no Rust slice has, so these fields are false of the real functions at the top of that range and under memory exhaustion (by reading). The two AEAD fields are false well below that, by reading. `aead::encrypt` panics on a `Vec` capacity overflow once its padded ciphertext (`16 * (n / 16 + 1)` bytes for an `n`-byte plaintext) exceeds half of `isize::MAX`, because appending the 32-byte tag asks the standard library's `Vec` growth for twice the buffer's capacity: from a plaintext of `2^30 - 16` bytes on a 32-bit target, a length a real slice can have (by reading, an estimate: the panic is reached only where about 3 GiB of allocations, three regions of about 1 GiB each, fit; otherwise an allocation failure aborts first), and `2^62 - 16` on 64-bit. The growth rule was read in the standard library source of the nightly-2026-06-01 toolchain, and a stand-in allocator emulating the same calls behaved so on 64-bit under that toolchain and under stable 1.98.1; those runs were made outside the tree and cannot be reproduced from it, no test in the tree holds the edge, and the 32-bit figure is the same arithmetic, not run. `Vec`'s growth strategy is an implementation detail that the standard library does not document as a guarantee, and CI builds with an unpinned stable toolchain, so the edge is stated for the versions read, not by contract. The seal also panics where the associated data plus the padded ciphertext exceed `isize::MAX`. `aead::decrypt` panics, by reading of `sha2` 0.10.9, once the associated data plus the ciphertext before its tag reach `2^61 - 64` bytes on a 64-bit target built with overflow checks (with the 64-byte inner-pad block the hashed input reaches `2^61` bytes, whose bit length overflows a `u64`); no 32-bit input reaches that, and with overflow checks off the bit length wraps and the open returns. Because both AEAD fields are stated for every length and are false of the shipping AEAD by reading, a theorem that takes either of them, directly or through `EncryptContracts`, `DecryptRatchetContracts` (and so `EstablishResponderContracts`), `OracleOf` or `DecryptOracleOf`, is conditional on a proposition about the real functions that does not hold; as stated, it says nothing about the shipping code at any length, not only at the lengths where the AEAD fails. That includes the lifecycle T1 theorems for `encrypt`, `decrypt` and `establish_responder` and every result that takes `OracleOf` or `DecryptOracleOf`. Restating the two with length premises (for the seal, `|ad| + 2 * |plaintext| + 64 <= isize::MAX`; for the open, `sha2`'s bit-length bound) and deriving those premises from the lengths each call passes, where they follow, is planned and not done; the theorems as stated will be kept beside the restated ones. A bound on the plaintext will remain a premise on the caller's input, since `Session::encrypt` refuses no plaintext by size, and on a 64-bit target so will a bound on a frame the theorem does not build, since `Session::decrypt` refuses no frame by size. The AEAD seal also carries its length bound, 48 bytes over the plaintext | fields of the four contract records, already assumed by the lifecycle T1 theorems ("The Session unit's primitive contracts are totality assumptions", above). Their bodies and those of their seven shapes over an interpretation (`UnitSatisfiabilityJoint.lean`) carry `#print` pins in `UnitOracleJoint.lean`, so a change to the text of one, such as the 48 bytes, fails the build. `tacenta-core/tests/rng_fill_counts.rs` drives the functions the seven predicates name over edge and sampled inputs and checks the length bound; that is a test on the inputs it tries |
| `SignFillsOnce64`, `KemShape` | `xeddsa::sign` fills one 64-byte buffer and touches the RNG nowhere else; `kem::encapsulate` refuses an invalid key before it reads the RNG and otherwise fills one 32-byte buffer | read from the source by the integration screen (`UnitLifecycleIntegrationScreen.lean`), not proved; tested on the shipped source by `tacenta-core/tests/rng_fill_counts.rs`, which counts every call of a counting random source and checks that a second source type with the same bytes gives the same result. The same test holds `GenerateFillsOnce64`. The test uses fixed inputs (four secrets and seven message lengths for `sign`, one key pair, seven wrong lengths and fifty sampled keys for `encapsulate`) and two random source types, where the laws are stated for every source type. It does not test the two view laws or the inputs at the failure edges the totality row records. It runs at the width of the machine that runs it: no CI job runs it or compiles it at 32 bits (the `armv7` job runs `cargo check --locked --workspace --target armv7-linux-androideabi`, which compiles no test target; its `i686` step runs `decrypt_premises` alone), so that it does not depend on the width of `usize` is by reading only |
| `DhViewInjective` | the byte views of `dh::PrivateKey` and `dh::PublicKeyBytes` the caller chooses are injective | new; by reading, each real type has an injective view (its wrapped bytes), which also meets `DhCodecOf`; a result applies to a caller's view only if that view is injective |
| `KemViewInjective` | the byte view of `kem::KeyPair` the caller chooses is injective | new; by reading, the real type has an injective view (its serialised bytes); a result applies to a caller's view only if that view is injective |

**Four laws suffice for `DecryptOracleOf`.** `DecryptOracleOf` (`UnitLifecycleDecryptRatchetT3.lean`), the four clauses of
`OracleOf` that `decrypt_ratchet_refines` and `decrypt_ratchet_refines_complete` take (`dhPublic`, `dhAgree`, `aeadOpen`,
`random32`), follows from four of the eleven: `DhCodecTotal`, `DhAgreeTotal`, `AeadOpenTotal` and `DhViewInjective`
(`decryptOracleOf_of_laws`, `UnitOracleDecrypt.lean`); `random32` needs no law at the byte-stream source. The four are
sufficient and not shown necessary: of `DhCodecTotal` the proof uses only the `public_key` conjunct, and injectivity is
more than the clauses need. The lemma builds
its oracle from the per-clause lemmas over `InterpO.decrypt`, an interpretation whose DH and AEAD-open constants are the
real ones (bound to the three totality predicates by `decryptInterp_laws_iff`), and does not go through `oracleOf_of_laws`.
Its statement takes only those four laws, so the other seven, `DhIdentityTotal`, `AeadSealBounded`, `KemDecapsulateTotal`,
`XeddsaVerifyTotal`, `SignFillsOnce64`, `KemShape` and `KemViewInjective`, are not hypotheses of this route to
`DecryptOracleOf`; that is held by its statement pin. Its axiom pin shows in addition that the witness oracle is built
without the KEM, signing, identity-test, AEAD-seal and KDF constants, a property of the proof and not of the statement. They remain assumed wherever `OracleOf` or `OracleOfGuarded` is used, which includes every
lifecycle and dispatch theorem that takes `OracleOf`. The model frame lemma `decrypt_oracle_frame`
(`tacenta-model/Model/LifecycleFrame.lean`) shows that `Model.Lifecycle.decrypt` reads only the oracle's `draws`,
`braidKem`, `dhPublic`, `dhAgree` and `aeadOpen`, so the oracle fields this route takes from the model's toy primitives, or
sets to refusals, are not read by the model's `decrypt`. The four laws keep the status the table gives them: assumed, not
proved of the shipped functions; one of them, `AeadOpenTotal`, is false of the shipping open by reading on a 64-bit target built with overflow checks (the totality row above), so the results that take it are, as stated, conditional on a proposition that does not hold. Not checked: which KEMs meet those agreements; the lemma lets the caller choose the KEM
and shows nothing about it. That the four laws, the contract records and `DecryptRatchetAgreements` at the oracle's `braidKem` hold
together is shown at one witness, under named laws with a model, in the `decrypt_ratchet` section below ("The hypotheses
together, at one witness").

The two view laws are conditions on the views a caller passes, not on the primitives. Each of the seven clauses the
integration screen left open says that a primitive returns and that the view of its result depends only on the views of
its arguments (the other five also count random draws); without an injective view a primitive could give two keys with
the same bytes different answers, and no oracle could match it. Lean cannot show that an injective view of an opaque
type exists at the real constants; the joint model has one. The laws are stronger than the clauses need: functionality
on views would do, and `DhCodecTotal` includes the totality of operations no clause mentions.

**What is shown about the laws.** `oracleLaws_hold_jointly` and `oracleOf_joint_model` exhibit one interpretation of the
opaque constants (`InterpO.model`, `UnitOracleModel.lean`) that meets the eleven laws, the axiom base of the four
records (`AxiomBase`), the DH codec and `GenerateFillsOnce64` together, and in which the twelve clauses and the guarded
clause hold for an oracle that refuses an input of each primitive that can refuse and whose KEM encapsulates at an
accepted key. The interpretation extends the joint one of the previous subsection by `xeddsa::sign`, which no record
reached before, and changes the DH and KEM key types from `Unit` to 32-byte arrays so that the DH codec can hold. Its
primitives are toys: agreement is an exclusive or, sealing puts a zero byte in front, the KEM secret is its random
input, a signature is the secret followed by zeros, and the KDFs, which it keeps from the joint interpretation, return
zero bytes (`hkdf_sha256` an array of zeros of the requested length, `hmac_sha256` 32 zero bytes), so every key it
derives is zero. Each refuses some inputs and accepts others, and each round trips:
it opens what it seals, decapsulates what it encapsulates and verifies what it signs. They ignore inputs the real
primitives depend on: opening ignores the keys and the associated data, verification ignores the message, and
decapsulation ignores the key pair. They do not refuse the inputs the real primitives refuse: the real agreement refuses
a low-order peer key and agrees a key with its own public key, and the model's witnesses `zero32` and `one32` are
low-order points that the real agreement and identity test both refuse. They are not secure.

**The sense.** The same as for the records: `oracleOf_of_laws` holds under the laws for every assignment of the opaque
constants, and the laws hold under one, so a derivation of `False` from them at the real constants would become a
derivation of `False` from facts true in the model once the constants are replaced. That step is an argument about
derivations and not a theorem inside Lean. No compiler-trust fact in the import closure mentions an interpreted constant,
directly or through a definition: that covers the unit's 143 and the 11 in `SessionUnitSpqrT3.lean` and
`SessionUnitTripleT3.lean`. `xeddsa::sign`, which `InterpO` adds, is one of the uninterpreted constants of the unit. The
classification audit of `check-session-satisfiability-negatives.sh` covers `Interp.real` and the four records; it is not
run for `InterpO.real` and `OracleOf`. It does not say that the real primitives meet the laws or that the oracle computes
X25519, the identity-key rule, the AEAD, ML-KEM or XEdDSA.

The oracle that inhabits the record is the code read through the byte views (`oracleOfLaws`): each primitive's verdict is
the code's answer on arguments with those bytes. So `OracleOf` asks of the code only that each primitive returns, that its
result depends only on the bytes of its arguments, and that it reads the random source in the stated order. It ties the
dispatch theorems to the code's own primitives and to no specification of X25519, the AEAD, ML-KEM or XEdDSA. The oracle
`oracleOf_of_laws` supplies is defined from the real primitives, so the record carries no content beyond the laws above.
Whatever a dispatch theorem proves with it is a statement about the model run with those primitives' own answers.

**What is not covered.**

- Only the byte-stream source (`byteRng`, `byteTrace`, from the integration screen). `OracleOf` reads the RNG through a
  trace of 32-byte draws, and nothing here concerns another source, the operating system's generator included.
- No consumer takes `OracleOfGuarded`. The dispatch theorems take `OracleOf`, whose KEM success clause binds the code only
  where the model predicts a success. The recommended migration is to move `OracleOfGuarded` next to `OracleOf` and have
  the consumers take it, using `.toOracleOf` where they need the old record; `kemClauses_of_guarded` shows the old clause
  follows. Not done here.
- The other records the dispatch theorems take (the per-run evidence, the counted Braid agreement) are not decided here,
  so these results alone do not make any dispatch theorem non-vacuous (`GAP-REGISTER.md`, row
  `DISPATCH-EVIDENCE-VACUITY`).
- `OracleOf` still leaves the oracle's `dhAgree` free off 32-byte arguments (`E2E-04-SAME-EPHEMERAL-MODEL`); deciding its
  clauses does not change that.
- The gate that looks for a hypothesis nothing satisfies (`check-hypothesis-witnesses.sh`) reads the sections of
  `CLAIMS.md` whose heading names a tier or a decoded state, and the section of these results is not one of them, so it
  does not read `oracleOf_of_laws`, `oracleOfGuarded_of_laws` or `decryptOracleOf_of_laws`. A hypothesis added to any of
  them is held by the statement pin of the theorem and by no other gate. That the eleven hypotheses of the first two hold
  together is argued from `oracleOf_joint_model`, a theorem about `OracleLaws` at a model, by the argument about
  derivations above; the four of `decryptOracleOf_of_laws` are among them.
- These results have been read by their writer and by tool-assisted readers working for the maintainer; no reviewer
  independent of the maintainer has read them.

### The Braid's preservation theorems: one new law on each translation, and what they do not cover

`BraidPreserve.lean` and its session-unit port show that every successful `send`, `receive` and
constructor of the Braid gives a state that has `State.sized` from one that has it, and so
`State.ct1_bounded` and, on the unit, `State.decoders_bounded` (`CLAIMS.md`, "Proved (the ML-KEM Braid
keeps the two premises its receive theorems take)" and the two sections after it). They assume the
following and leave the following open.

- **One law about the erasure decoder on each translation, assumed.** On the standalone translation it is
  `BraidPreserveDecoder.NewMsgLen`: a decoder that `Decoder::new(m)` builds never returns a message longer than `m`,
  however many chunks it is given and however often it is cloned. It is true of the real decoder, whose
  `message` ends in `out.truncate(self.size)`, and no proof here checks it against the real crate.
  `BraidPreserveWitness.lean` shows one implementation of the opaque erasure operations satisfies it together with
  `ErasureAgrees`, `ErasureCloneAgrees` and the seven erasure totality assumptions, for an arbitrary `Usize` and so at
  both platform widths. On the session unit the decoder is translated, so the law becomes two laws, one about
  `Vec::truncate` and one about `usize::div_ceil`: `TruncateLen` (`Vec::truncate` of `n` returns at most `n` elements;
  it is `TruncateTotal` of the table above with the length bound added, and the bound is new to this ledger) and
  `DivCeilValue` (one of the five laws above, not new). `TruncateLen` follows from the prefix property the joint
  model of `UnitSatisfiabilityJoint.lean` already gives `truncate` (`truncateLen_model`). Each is consistency of a
  statement and not a model of the real operation. Dropping the clause `Good 4096 ct1_dec`, replacing 4096 by 4097 in
  it, dropping `DivCeilValue` from `Laws`, and strengthening the model's law by one byte each made the corresponding
  proof fail, which is the check that each is used and is not slack.
- **The two-field mirror does not imply `State.sized`.** `ct1_bounded` and `decoders_bounded`, and so
  `SessionUnitBraidImportInv.Braid.Inv`, do not say that the decoder that makes `ct1` is sized for at most 4096 bytes.
  A `HeaderSent` state whose decoder is sized for 4097 bytes meets both, and the chunk that completes the decoder makes
  a `ct1` of 4097 bytes. That step is not a Lean theorem: the Lean side states only that the mirror does not imply
  `State.sized` (`inv_not_sized`), because the translated `Decoder::message` is not computed in Lean. The theorems
  are about `State.sized`, which adds the clause. `Braid::invariant` rejects such a state, so no decoded or
  constructed Braid is one. The step was run on the real crate in a scratch tree; the test is not committed (see
  "Waiting on the next re-translation window").
- **Not `Braid::invariant`.** `State.sized` has none of the clauses of `Braid::invariant` that the receive theorems
  do not use: the exact lengths of `header`, `ct1` and `ek_vector`, the encoders' sizes, `epoch >= 1` and the key
  pair's validity. No theorem shows that the crate's own `invariant` is preserved.
- **A decoded Braid is covered on the session unit only.** The standalone translation leaves `Decoder::invariant` and
  `Decoder::size` opaque, so nothing there says a restored decoder is sized for its protocol constant.
- **The Braid's own operations, not a session.** A session state is not shown to hold a Braid reached by them.
- **The refinements keep their other premises**: the epoch headroom `epoch + 1 < u64::MAX`, the honest-chunk condition
  (the unspliced stream) and the relation of the real state to a model state. A live encoder is a premise of the send
  refinements and not of the receive refinements.
- **What holds the statements.** Each result has an axiom pin that `attest.py` requires. The statements and the
  definitions that carry the claim (`State.sized`, `Braid.Run` with its constructors, `Good`, `Laws`) are held by
  `#guard_msgs in #check` and `#guard_msgs in #print` pins that the build checks and `attest.py` requires to exist
  (`REQUIRED_STATEMENT_PINS`). `attest.py` reads a pin's message only to refuse a cut-off `⋯`, so a statement changed together with its pin's
  expected message is accepted, and weakening a result that has no pin fails no gate. The results with no
  statement pin are `api_newMsgLen`, `model_for_both_widths`, `message_length_le`, `Good.msg`, `Good.add` and
  `Good.clone`; the other results have one.

### The Braid refinement agreements of the Session unit: what is assumed, and what has a model

`step_send_refines`, `Braid.send_refines`, `step_receive_refines` and `Braid.receive_refines`
(`SessionUnitBraidT3.lean`) rest on assumptions that this section lists, with what the build holds
about each (`CLAIMS.md`, the section on the Braid refinement agreements).

**Assumed, about opaque constants and the KDF.** Six agreements relate the KEM and the KDF to `Model.Braid.Kem`
and `Model.Kdf` (the KDF's two are about translated definitions since the KDF change (ADR-0010), and are proved of them by
`UnitLifecycleKdf.braidHkdfAgrees` and `braidHmacAgrees`, though these theorems still take them): `KemAgreesFor K`, `KemLenAgrees K`, `ValidateEkAgrees K`, `KemCloneAgrees`,
`BraidHkdfAgrees` and `BraidHmacAgrees`. A seventh premise, `KemDrawsSucceed`
(`UnitSatisfiabilityBraidAgreements.lean`), says the real key generation and `encapsulate1` each succeed for
some RNG; the state witnesses take it because the two-sided `KemAgreesFor` admits a KEM that refuses every
call. It holds in `Interp.modelT3` (`modelT3_kemDrawsSucceed`); of the real wrapper it is assumed, and
every Braid test that completes an agreement exercises both calls, which is testing and not proof. With
`KemDrawsSucceed`, the premises still admit a KEM whose decapsulation and second encapsulation half refuse
every input, which is read off the clauses (each is two-sided and the premise speaks only of the two
draws); the interpretation that shows it is not in the tree. Nothing assumed implies that transitions (5),
(9), (11) or (12) can succeed, or that an honest run completes an epoch, and a claim that one does needs
its own premise.
Nothing shows that the real ML-KEM wrapper or libcrux satisfies its four; the two KDF agreements are proved of
the unit's translated KDF (`UnitLifecycleKdf`). What is shown is that they are consistent: one interpretation of the unit's opaque
constants satisfies all six together with `KemDrawsSucceed`, at `Model.Braid.toyKem`, together with the axiom-level fields of the session records,
by the substitution argument above, which is an argument about derivations and not a theorem inside
Lean. `K` is existential in `KemAgreesFor K`, so the model's choice of `toyKem` says nothing about the real
`K`. `ValidateEkAgrees K` holds of the real `validate_ek` only for a `K` whose `hashEk` also folds in the
coefficient check the real function makes after the hash; such a `K` exists, but the check is read from the
source (`kem/src/lib.rs`) and no test runs a vector that matches the hash and fails the check.

**A KEM model read off the wrapper, and the laws it rests on.** `Translation/UnitKemWrapperModel.lean` builds one `K`,
`wrapperKem`, whose operations call the wrapper's opaque functions on byte views of their arguments (the model's randomness
read as the byte-stream source `byteRng`; the private part the 64 key-generation bytes; the encapsulation secret the 32
encapsulation bytes followed by the header; `hashEk` the hash `validate_ek` accepts, or the empty string where it accepts
none, so the coefficient check after the hash is folded in), and proves `KemLenAgrees`, `KemAgreesFor` and
`ValidateEkAgrees` at it from eight laws (`CLAIMS.md`, the section on that model). `KemCloneAgrees` mentions no `K` and is
one of the laws. Each law is a statement about opaque `tacenta_kem` constants, and each is assumed:

- `LawKemConstants`: `HEADER_LEN`, `EK_VECTOR_LEN`, `CT1_LEN` and `CT2_LEN` are 64, 1536, 1408 and 160. Read from the source
  (`kem/src/lib.rs`; `HEADER_LEN` and `EK_VECTOR_LEN` are libcrux's `pk1_len()` and `pk2_len()`), and exercised by the
  crate's test `the_sizes_are_the_specifications_sizes`.
- `LawGenerateSeeded`: from any source that answers, `generate` returns what it returns from the byte stream of some 64
  bytes. Read from the source (`generate` draws one 64-byte seed and hands it to libcrux); that libcrux's key generation
  is a function of the seed is not checked.
- `LawGeneratedKeyPair`: a key pair generated from 64 bytes has a 64-byte header and a 1536-byte vector that `validate_ek`
  accepts together, and `decapsulate` returns on it for any ciphertext halves of 1408 and 160 bytes, including halves no
  encapsulation produced. The lengths and the acceptance are exercised by the crate's tests
  (`the_sizes_are_the_specifications_sizes`, `validate_ek_accepts_the_real_key_and_rejects_a_substitute`); that
  `decapsulate` returns on every such input is not checked.
- `LawEncapsulate1Seeded`: from any source that answers and a 64-byte header, `encapsulate1` returns what it returns from
  the byte stream of some 32 bytes. Read from the source; that libcrux's first half is a function of the header and the 32
  bytes is not checked.
- `LawEncapsulate2Fresh`: `encapsulate2` returns, `Ok` or `Err`, on a state `encapsulate1` produced and any 1536-byte
  vector, including a vector that `validate_ek` refuses. So the law assumes that libcrux returns on inputs outside its
  stated precondition: libcrux deserializes the vector's 12-bit coefficients without reduction, so they reach 4095, and it
  states `|c| <= 3328` for the arithmetic; the wrapper leaves that side of the precondition to `validate_ek`
  (`kem/src/lib.rs`, the comment in `encapsulate2`). The Braid never calls `encapsulate2` there, because it validates the
  vector first. The proofs need the law in this form: `EncapsRefines` quantifies over every 1536-byte vector. A probe by a
  reader of these results, outside the tree, made 12,000 such calls on the NEON and portable backends, every coefficient
  at 4095 among them, and each returned `Ok`; the AVX2 backend was not run. That is testing, not proof, and no test in the
  tree makes such a call. The coefficient-bound refusal of `encapsulate2` is inside this opaque function, so it enters only
  here, and the law says nothing of whether it refuses a fresh state.
- `LawValidateEkTotal`: `validate_ek` returns on a 64-byte header and a 1536-byte vector.
- `LawValidateEkUnique`: two 64-byte headers with the same first 32 bytes that `validate_ek` accepts with one vector are the
  same bytes. Read from the source: libcrux compares the last 32 bytes with a hash of the vector and the seed.
- `LawKemClone`: `KemCloneAgrees`, as stated above.

One interpretation, `Interp.modelShipped`, satisfies the eight together with every other law the decrypt joint statement
takes (`decrypt_wrapper_laws_model`), in the substitution sense of the section on the four contract records. In it key
generation and encapsulation ignore the source and return constant bytes and nothing refuses, so it shows the laws
consistent, not that the wrapper meets them, and it exercises no refusing arm of `wrapperKem`. Not shown: a key pair or
state restored by `from_bytes` has no model value at `wrapperKem`, so the refinement relations at it are shown only for
values `generate` and `encapsulate1` produce; `KemDrawsSucceed` and `Model.Braid.Kem.Correct` are not shown at it. One
further law about the wrapper, `LawGenerateSucceeds` (`generate` returns `Ok` from some 64-byte stream), is taken only by
the witness whose Braid holds a key pair ("The hypotheses together, at a Braid that holds a key pair", below), where it is
recorded.
So the KEM side of the decrypt joint statement at `wrapperKem` does not rest on the eight laws alone. The corollary also takes, through the bundle's `braid` field (`BraidReceiveAxiom`), `SessionUnitBraidT1.KeyPairDecapsulateTotal`, `Encapsulate2Total` and `ValidateEkTotal`, which say that `decapsulate`, `encapsulate2` and `validate_ek` return on every value, restored key pairs and states and inputs of any length included; the eight laws do not narrow them, and those three imply the totality parts of `LawGeneratedKeyPair`, `LawEncapsulate2Fresh` and `LawValidateEkTotal`. They were in the bundle before these results and are not shown false; the first is the statement `GAP-REGISTER.md`, row `KEM-STORED-STATE-TOTALITY`, records as sampled and not shown total.

**Assumed, about two library functions.** The erasure coder's agreement with the model, `ErasureAgrees`, is a
theorem about the translated coder under two laws, because the translation leaves two library functions
opaque: `usize::div_ceil` at divisor 32 returns `(a + 31) / 32` (`DivCeilValue`, already a field of
`EstablishResponderContracts`), and `Vec::truncate` keeps the prefix (`TruncatePrefix`, which strengthens
the existing `TruncateTotal` from returning to returning the prefix). Both are the documented behaviour of the
standard library functions, and both hold in the interpretation above. The proof is about the
translation: `Vec::with_capacity` never fails there, where the real function panics for an absurd
capacity.

**Not shown.** That a send or a receive keeps `ct1_bounded`, `decoders_bounded`, `EncodersLive` or the epoch
headroom: the state witnesses are single steps. That `MsgRefines` and `HonestChunk` hold of a message a peer
sends: `MsgRefines` holds of a real chunk of any content when the decoder needs at least one chunk, so
`HonestChunk` is the only hypothesis that excludes a spliced stream. That a decoder restored by
`Decoder::from_bytes` refines a model decoder: one that holds chunks of no common message refines none,
so the refinement theorems apply to states reachable from a fresh Braid and to restored states equal to
such a state.

### The `decrypt_ratchet` refinement: what it assumes, and the path its first form left open

`decrypt_ratchet_refines` (`Translation/UnitLifecycleDecryptRatchetT3.lean`; `CLAIMS.md`, the section on
`decrypt_ratchet` with the eviction retry loop) relates the private transaction behind `Session::decrypt` to
`Model.Lifecycle.decryptRatchet` under the hypotheses in its statement, and its complete form
`decrypt_ratchet_refines_complete` (`Translation/UnitLifecycleDecryptRatchetCompleteT3.lean`) takes the same hypotheses
(`decrypt_ratchet_refines_complete_implies_refines`) and closes the one path the first form left open. This section
lists what they assume; it holds for both forms.

**Assumed, about opaque operations.** `DecryptOracleOf` is the four clauses of `OracleOf` the transaction uses: the DH
public key and the DH agreement of `tacenta_boundary::dh`, the AEAD open of `tacenta_boundary::aead`, and the 32-byte draw
of `random_secret` from the caller's random source. `DhCodecOf` says the byte views of the two opaque key types agree with
`PrivateKey::from_bytes`, `PublicKeyBytes::from_bytes` and `PublicKeyBytes::as_bytes`; it makes `PrivateKey::from_bytes`
injective on bytes, which holds of the locked `x25519-dalek 2.0.1` because `StaticSecret::from` stores the bytes unchanged
and clamps at use, and would stop holding of a release that clamps at construction. `DecryptRatchetAgreements` assumes
round trips of the opaque `zeroize::Zeroizing` wrapper at 32, 64, 80 and 96 bytes, the HMAC and HKDF agreements with
`Model.Kdf` (as `CLAIMS.md` records for the Triple and the Braid), the KEM agreements of the Braid section above, and two
laws about `Vec::pop` and `Option::as_mut` (the paragraph on the sparse store below). Those
include `ValidateEkAgrees K`, which holds of the real `validate_ek` only for a `K` whose `hashEk` also folds in the
coefficient check, so the model step this theorem relates to is the model run with that `K`. None is shown of the real
X25519, AEAD, ML-KEM or `zeroize` code; the HMAC and HKDF agreements are proved of the unit's translated KDF
(`UnitLifecycleKdf`), and `UnitLifecycleKdf.decrypt_ratchet_refines_complete_of_kdf` states the complete refinement
without them. What is shown is that they are consistent: one interpretation of the unit's
opaque constants, `Interp.modelDecrypt` (`Translation/UnitLifecycleDecryptRatchetScreen.lean`), satisfies all of them
together with the axiom-level fields of the session records and the laws above, with an agreement that refuses the
all-zero key and an AEAD that refuses the empty ciphertext. That is the substitution argument above, about derivations
and not inside Lean; `decrypt_ratchet_refines_from_shapes` composes the shapes with the run inside Lean, so the
substitution step itself is the only part outside it. `DhCodecOf` and the DH and AEAD clauses had no model before this
result. The joint decision of the clauses of `OracleOf` ("The clauses of `OracleOf`", above) gives a second, separate one,
`InterpO.model`, in which `DhCodecOf` and all twelve clauses of `OracleOf` hold together; there the oracle is read off
the interpretation's primitives through the byte views, while here it is a fixed toy, `oracleDecrypt`, with the identity
public key, an agreement that returns the private key and refuses the all-zero public key, and an AEAD open that returns
the empty plaintext and refuses the empty ciphertext. Neither model shows anything of the real X25519 or AEAD.

**Assumed, about the session contract records.** The theorem takes `DecryptRatchetContracts` and the class
`DerivedKeysModel`. The records are described in the section on the four contract records above. Three of their fields,
`SessionUnitSpqrT1.ZeroizeTotal`, `SessionUnitBraidT1.ArrayZeroizeTotal` and the `Vec::zeroize` conjunct of
`SessionUnitSpqrT1.VecRetainTotal`, say that `Array::zeroize` and `Vec::zeroize` return at the instances the unit passes to
them; that the real functions do is assumed (the paragraph "Three fields are stated at the unit's instances"). Before they
were restated they quantified over every `Zeroize` record, which the real functions do not support. The records also hold
`Random32Total` and `MessageKeyMaterialRoundTrip`, a round trip of the `zeroize::Zeroizing` wrapper at a tuple of three
arrays.

**The sparse store: laws about opaque operations, in place of two agreements about translated functions.**
`SessionUnitSpqrT3.VecRetainAgrees` (the chain-table and skipped-key scans of `set_chains` and `clear_old_epochs` keep
what the model keeps) and `SessionUnitSpqrT3.RemoveSkippedAtAgrees` (the removal helper returns the key at the index it
removes and the vector with that index erased) are statements about translated functions. The theorems do not take
them: the proof derives them (`DecryptRatchetAgreements.vecRetainAgrees`, `.removeSkippedAtAgrees`, through
`UnitSatisfiabilitySpqrSessionLaws.lean`) from five laws about opaque operations, all assumed: `LawPop` (`Vec::pop` of a
non-empty vector returns the vector without its last element) and `LawAsMut` (`Option::as_mut` returns, at every type),
the two fields `pop` and `asMut` of `DecryptRatchetAgreements`; and three laws the contract record already states,
`LawCapacity` (`Vec::capacity` returns) and `UnitSatisfiabilityRatchet.LawVecZeroize` (`Vec::zeroize` returns at the
chain table and the two skipped-key stores), the first two conjuncts of `SessionUnitSpqrT1.VecRetainTotal`, and `SessionUnitSpqrT1.ZeroizeTotal`
(`Array::zeroize` returns at the blanket `u8` instance on a 32-byte array). `RemoveSkippedAtAgrees` uses the pop and
array laws; `VecRetainAgrees` uses all five. None of the five is proved of the real functions or tested; each is assumed,
and matches the documented behaviour by reading only. What is shown of them is consistency: they hold in the joint model `Interp.model`, in
which every axiom-level field of the four contract records holds (`spqrSessionLaws_model`), and in the interpretation of
`UnitSatisfiabilityZeroizeScope.lean` whose wipes propagate a failing element's failure (`faithful_SpqrSessionLaws`), in the
substitution sense above; and an interpretation whose `Vec::pop` leaves a vector unchanged fails them
(`spqrSessionLawsShape_fails_of_noop_pop`). The loop theorems `receive_with_eviction_loop_refines` and
`receive_with_eviction_refines`, the refusal theorems of the complete form and the session unit's sparse and Triple
refinement theorems still take the two agreements as hypotheses (`GAP-REGISTER.md`, row `SESSION-SPARSE-AGREEMENTS`), and
so does their composition `UnitLifecycleSparseSkipKindT3.skip_message_keys_refines_detailed`, which takes
`VecRetainAgrees` alone.
`ErasureAgrees` follows from the two laws about `usize::div_ceil` and `Vec::truncate` above.

**The random source.** The random source holds at least one draw; the model's ceiling refusal for an exhausted source has
no Rust counterpart. The source is read through a function `trace` that gives the draws left in its value, so the theorem
applies to a source whose value carries them, as the byte-stream source of the screen does. A source with no state of its
own, such as `OsRng` or the handle `ThreadRng` holds, returns the same value after a draw, and `DecryptOracleOf.random32`
and the draw field of `DecryptRatchetRun` cannot both hold for it. So the shipped call with such a source is outside the
formal statement, and is related to this theorem only by an argument outside Lean that takes the bytes the source returns
during the call as its draws. The same holds for every `OracleOf` theorem of the lifecycle layer.

**Per run.** The run's agreement chunk is a codeword of one source that fits the decoder it is fed to (`IncomingChunkRefines`,
`HonestChunk`), so a run whose chunk is spliced or inconsistent is outside the theorem whether it is refused or accepted.
At a session `establish_initiator_for` returned, `HonestChunk` holds for every message (`honestChunk_established`: its
Braid is in `KeysUnsampled`, which holds no decoder); the chunk relation for a frame that carries an agreement chunk and the
draw stay the caller's there too.
Each skipped-key store is at most `2^32 - 1 - 2000` long. The model state meets `RetryReceiveBounds`: its event counter,
epochs and chain counters leave room, its chain table has room for two more entries, and at most one skipped key in each
store matches the header (`Ratchet::invariant` and `State::invariant` supply the last; the event bound is one stricter than
the invariant's). Three runs meet all of these at both platform widths: one whose model step refuses at the first agreement,
one whose model step succeeds without an eviction round, and one whose stores are non-empty and whose model step enters the
eviction retry loop, evicts one key and retries (the outcome of the retry is not stated, and no run reaches an empty
eviction, a second round or a switch between the stores). A fourth (`UnitLifecycleDecryptRatchetCompleteScreen.lean`) meets
them at both widths too and is one whose model step is a Triple refusal that is not a full store, returned by the first
attempt; no run reaches such a refusal in a retry round, or a sparse refusal. Each shows the model side of the run, not
which branch the shipped code takes; for the fourth, `generated_reaches_open_path` also gives the generated output under
the boundary records. The witness states meet these hypotheses and not `Ratchet::invariant`: the third run's classical
store repeats one key, and the second, third and fourth runs hold a receiving chain without a sending chain, which the
invariant refuses.

**The per-run bounds, from `Session::invariant`.** `decrypt_ratchet_refines_of_invariant`
(`Translation/UnitLifecycleDecryptRunBounds.lean`) restates the complete form with `Session::invariant` in place of
`DecryptRatchetHeadroom` and of the run's receive bounds. Of the eleven fields of `RetryRunBounds`, the invariant alone gives
five (the two match bounds, the chain-table room, the two store bounds), the invariant with the assumed sparse epoch ceiling
two more (the two kept-epoch bounds), the model gives one (the epoch label of a Braid receive's output, `Model.Braid.receive_output_epoch_lt`), and three
are fields of `CounterHeadroom`, which also holds the run's Braid epoch ceiling; `CounterHeadroom` is assumed ("The headroom
records", *Counter ceilings, assumed*, above). The chunk, `HonestChunk` and draw conditions stay hypotheses
(`DecryptRatchetRunInputs`). Its hypotheses hold together at the joint witness below under the same laws
(`decrypt_of_invariant_hypotheses_jointly_satisfiable`), and at a session with stored keys, open chains and counters away
from zero (`UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys`), built for the
hypotheses as that witness is.

**Tested only: the run premises on shipped runs.** `tacenta-core/tests/decrypt_premises.rs` reads the state of real
sessions before each `Session::decrypt` call, from `Session::export`, and asserts the runtime form of the bounds of `RetryRunBounds` above and the four ceilings of `CounterHeadroom`:
the event counter, the sparse epoch, the chain and skipped-key epochs, the chain counters, the room in the chain table and
in both stores, at most one stored key matching the header in each store, and the Braid epoch (the output's key epoch only
through the Braid's own, which `step_receive` never lets it exceed). It also asserts, at each call, that the random source is
read as `Model.Lifecycle.decryptRatchet` reads it (no draw when the dispatch, the terminal guard, the decoder or the
incoming agreement refuses; one 32-byte draw from the first agreement on, kept on a later refusal), that a refusal leaves
the exported bytes unchanged, that a success changes them, and that `Session::invariant` holds before and after. The runs
start from the establishment of `session-e2e.json` and reach an accepted repeat, a pass-through success, the refusals of
a changed or low-order ephemeral, of a replay, of a frame beyond `MAX_SKIP`, of a forged tag, of an unknown type or
version byte, of a truncated frame, of an initial message sent to an initiator, of a low-order ratchet key and of a failed
agreement, and a full skipped-key store with an eviction. That is evidence about those runs, on the inputs tried; it is
not proof, and it discharges no premise for any other run. It runs at the width of the machine that runs it, and the
`armv7` CI job runs it once more at 32 bits (`i686-unknown-linux-gnu`); its bound checks are written to the 32-bit bound
at every width, so the 32-bit run adds the shipped library's behaviour at that width, and it has not been made locally.
It does not reach `IncomingChunkRefines` and `HonestChunk` (a chunk carries no source to read), a counter or epoch near
its ceiling or a store near `2^32 - 1` (no run builds one), a second eviction round, a switch between the stores, a
sparse refusal other than an out-of-order key after an eviction, or a frame naming an epoch the state holds no chain for.
Each premise check has a control that calls it outside any run: eight on a mutated copy of an observed state, three
(`classicalStore`, `sparseStore`, `sparseChainsRoom`) on the length arithmetic alone, with lengths no session holds, and
`sparseOutputEpoch`, whose bound is the Braid epoch's, through the `braidEpoch` check. Those controls show the checks can
fail; they show nothing of the runs. `Session::invariant` accepts a state with `events = u32::MAX - 1`, which is outside
`classicalEvents`; the test imports such a state and shows the check rejects it.

**The hypotheses together, at one witness.** `decrypt_hypotheses_jointly_satisfiable`
(`Translation/UnitLifecycleDecryptScreen.lean`) shows every hypothesis of `decrypt_ratchet_refines_complete`, with
`Session::invariant`, holding together at the real constants and the byte-stream source, at one oracle, one state pair,
one message and one source, for every codeword view, under a bundle of fifteen fields (`DecryptJointLaws K dh`, listed
in `CLAIMS.md`; fifteen counts fields, not distinct statements). Two interpretations satisfy all fifteen together, each a
model in the substitution sense of the section on the four contract records: `decrypt_joint_laws_model`
(`Interp.modelDecrypt` with `toyKem`), whose four KEM length constants are `toyKem`'s sizes (`CT1_LEN` 64, `CT2_LEN` 32,
`HEADER_LEN` 64, `EK_VECTOR_LEN` 64), and `decrypt_joint_laws_model_at_shipped_sizes` (`Interp.modelShipped` with
`shippedSizeKem`), whose four are the crate's (1408, 160, 64, 1536, `tacenta-core/kem/src/lib.rs`), with a model KEM of
those sizes. In both the KEM is a model that never refuses and returns constant bytes, not ML-KEM, and the X25519 agreement,
the AEAD open and the KDFs are toys or the model's own bytes. So the laws are shown consistent with the shipped KEM sizes;
that the real ML-KEM wrapper meets the agreements at some `K` is shown by neither model. At `wrapperKem`, the KEM model read
off the wrapper, the KEM agreements follow from the eight laws of the section on the Braid refinement agreements, which are
assumed; `decrypt_hypotheses_jointly_satisfiable_at_wrapperKem` is the joint statement at `wrapperKem` with those laws in
place of the agreements field, and `decrypt_wrapper_laws_model` satisfies its bundle in `Interp.modelShipped`. The witness's
Braid holds no KEM value, so that coupling is not exercised there; the second witness below exercises it at a held key
pair.

The proof restates, from the bundle, `DhCodecOf`, `DerivedKeysModel`, the axiom-level contract fields and thirteen of the
fourteen fields of `DecryptRatchetAgreements`; it derives the contract record's defined fields and `ErasureAgrees`, and
establishes `DecryptOracleOf` (from the four laws) and, at the witness, `Session::invariant`, `SessionRefines`,
`DecryptRatchetHeadroom`, the trace equation and `DecryptRatchetRun`. The oracle is the one `decryptOracleOf_of_laws`
builds, with its `braidKem` set to the KEM model `K` at which the Braid agreements are assumed, so the agreements are
stated at the same oracle's `braidKem`. The oracle `oracleOfLaws` builds carries `toyKem` before that choice, and by
reading the agreements fail there for the real KEM (`KemLenAgrees toyKem` asks the real `CT1_LEN` to be 64; it is 1408).
At this witness the coupling holds by construction: `K` enters only through the agreements (fields of the bundle),
`SessionRefines` (which holds for every `K`, the Braid being in `KeysUnsampled`) and the run (which does not depend on `K`,
carrying no chunk); the theorem holds equally at `K := toyKem`. At this witness the coupling is not tested; the second
witness below tests it at a Braid that holds a key pair. What the joint witness is not:

- The state is built for the hypotheses. It is `UnitHeadroomSatisfiable.sessionOf` with one key as both identities, the
  66-byte associated data `identity_ad` computes, no pending initial message, no established ephemeral key, no receiving
  chain and a Braid in `KeysUnsampled`. It passes `Session::invariant` under `ValidKeyShape` and `OptionEqU64Shape`
  (both laws of the bundle). It is not shown to be produced by `establish_initiator`, `establish_responder` or `import`.
- The laws are assumed, not proved of the shipped functions; they are sufficient and not shown necessary. That they hold
  together is shown in the substitution sense of the section on the four contract records, an argument about derivations
  and not a theorem inside Lean, in two models whose primitives are toys (one of them at the shipped KEM sizes).
- The oracle is the code read through its byte views (`oracleOfLaws` over `InterpO.decrypt`); nothing is shown of X25519,
  the AEAD, the KDFs, ML-KEM or `zeroize`.
- The run carries no agreement chunk; the chunk and honest fields of `DecryptRatchetRun` hold by their arm for a message
  without one. A run carrying a chunk into a decoder that already holds one is not reached.
- The model's step at the witness is not fixed by the laws. The message's ratchet key is 32 zero bytes, and the step refuses
  at the first agreement with `nonContributoryAgreement` if the oracle's agreement refuses that key
  (`invReal_model_refuses_of_agreement`); at this oracle that agreement is the real `agree` on the key
  `PublicKeyBytes::from_bytes` returns for 32 zero bytes (`invReal_agreement_is_real`), which no law states. By reading
  `tacenta-core/boundary/src/dh.rs` it refuses (`agree` returns `None` on a non-contributory result, which the all-zero key
  gives), and in the model interpretation it refuses. So the witness does not exercise the Triple receive, the AEAD, the
  eviction loop or a success; the earlier runs above do, over sessions that fail `Session::invariant`.
- Only the byte-stream source is covered (the paragraph on the random source above).
- `check-hypothesis-witnesses.sh` does not read the `CLAIMS.md` section of these results (its heading names no tier). A
  law added to the bundle, or a hypothesis added to `decrypt_ratchet_refines_complete`, is held by the `#print` pins of
  `DecryptJointLawsShape` and `DecryptHypotheses`, by `DecryptHypotheses.refines` and by the build, and by no other gate.
- These results have been read by their writer, a tool-assisted agent working for the maintainer, and by one
  tool-assisted reader working for the maintainer, whose findings were applied; no reviewer independent of the maintainer
  has read them.

No proof here chooses a width of `usize`, and no result depends on a compiler-trust axiom (`DecryptHypotheses.refines`
did, through the nine of the refinement, until 2026-10-21), so each result holds at both widths; no hypothesis of the set is width-dependent at this witness.

**The hypotheses together, at a Braid that holds a key pair.** `decrypt_hypotheses_jointly_satisfiable_at_wrapperKem_held`
(`Translation/UnitHeldKemWitness.lean`) shows the same hypothesis set at a second witness: the first witness's session
with its Braid in `KeysSampled` at epoch 1, holding a key pair `IncrementalKeyPair::generate` returned from a 64-byte stream
and the header encoder after one chunk, and a model session whose Braid holds the 64 bytes as its private part and the
bytes of the pair's `ek_vector` as its vector (`HeldKemAt`; the model Braid is the model's own transition (1) at that
randomness). There `SessionRefines` at `wrapperKem` is asked of a held value. What it compares by value: the model's
vector with the real vector's bytes, at every KEM model (`held_relation_pins_vector`), and the header hash, through
`hashEkOf`, `LawValidateEkUnique` and `validate_ek` accepting the generated pair (`held_key_agreements`), with the
lengths. What holds by definition: `wrapperKem`'s operations call the real `generate` and `decapsulate` on the held
bytes, so its key-generation part and its decapsulation clause (the real `decapsulate kp` compared with itself) hold by
unfolding `wrapperKem`, with only the totality of `decapsulate` on generated pairs from `LawGeneratedKeyPair`, and so
does `HeldKemAt`'s conjunct that the model Braid is the model's transition (1). The relation is false at `toyKem`
(`held_not_refines_toyKem`), a length mismatch (any private part not of 32 bytes), not a comparison of held bytes.
`Session::invariant` passes under the first witness's assumptions (`ValidKeyShape`, `OptionEqU64Shape`, `DhCodecTotal`),
`LawKemConstants` (`HEADER_LEN`), `DivCeilValue` (the encoder's size), `LawGeneratedKeyPair` (`key_pair_valid`) and
`LawGenerateSucceeds` (the key pair itself). `decrypt_hypotheses_with_chunk_at_wrapperKem_held` is pinned but not a
claim: a caller-selected run whose chunk (index 0, 32 zero bytes, a codeword of 1408 zero bytes by the real encoder) and
codeword view (a constant reading every chunk as that codeword) are chosen together; 1408 zero bytes is not a
ciphertext `encapsulate1` produces, `HonestChunk` asks nothing at that state, and the model's refusal discards the Braid
step. It is not a non-vacuity statement for chunks, which would take every chunk that fits the real decoder.

*Assumed, beyond `DecryptWrapperLaws`:* `LawGenerateSucceeds`, that `generate` returns `Ok` from the byte stream of some
64 bytes. It is a statement about one opaque `tacenta_kem` function and the Lean byte-stream source; none of the eight
wrapper laws gives it. Read from the source: `generate` draws one 64-byte seed and passes it to libcrux's key generation,
which does not refuse at that length (`tacenta-core/kem/src/lib.rs`); no test in the tree checks it. It follows from the
key-generation half of `KemDrawsSucceed` with `LawGenerateSeeded` (`lawGenerateSucceeds_of_kemDrawsSucceed`), and
`Interp.modelShipped` satisfies it with the wrapper bundle (`held_laws_satisfiable`), in the substitution sense.

What the second witness is not:

- The state is built for the hypotheses; the shipped code does not produce this combination of Triple and Braid states;
  the invariant admits it. `Session::encrypt` commits the Triple and the Braid together
  (`tacenta-core/session-unit/src/lifecycle.rs`, `self.triple = candidate; self.braid = braid_next`), so no session
  holds a Braid in `KeysSampled` beside a Triple that has sent nothing, as this one does. `Session::invariant` reads
  neither the Braid's authenticator (the zero keys here; `Auth::init` derives them by HKDF) nor the header its encoder
  carries, and `SessionRefines` does not relate that header to the key pair; only `HeldKemAt` does. The header message
  carries the model's MAC under the zero authenticator, where `Braid::send` computes it with the opaque HMAC. That the
  real `Braid::send` from `KeysUnsampled` under the zero authenticator lands on this Braid state was not attempted.
- No run carrying an honest chunk is shown: the chunk run is caller-selected (above). A run into a decoder that already
  holds a chunk is still not reached: `Session::invariant` at such a state (`HeaderSent` and the others holding a decoder)
  calls `Decoder::invariant`, a loop over the held chunks, and no result evaluates it on a decoder holding chunks. Not
  checked: whether that evaluation needs more than the erasure laws already assumed.
- No encapsulation state is held, so `EncapsRefines` is not asked at a held value; a responder state at `Ct1Sampled` is
  not built.
- The model's step is not fixed by the laws: both messages carry the all-zero ratchet key, and the step refuses at the
  first agreement if the real agreement refuses it (`held_model_refuses_of_agreement`, with `invReal_agreement_is_real`
  unchanged). The Braid step the model computes at the chunk message is discarded by that refusal. No Triple receive,
  AEAD open or success is reached.
- The oracle's other KEM fields are not related to `wrapperKem`; nothing is shown of ML-KEM; a key pair restored by
  `from_bytes` has no model value at `wrapperKem`.
- These results have been read by their writer, a tool-assisted agent working for the maintainer; no other reader has.

No proof here chooses a width of `usize`, and no result depends on a compiler-trust axiom (the pins), so each holds at
both widths.

**The path the first form left open.** On a run whose output is a Triple refusal with a reason other than a full store,
the first form says nothing about the model's step (`TripleRefusalOpen`; `tripleRefusalOpen_exactly` shows it holds of
no other output). The predicate constrains only the generated output, so it can hold where the model's step succeeds.
`triple_receive_refusal_refines` (`Translation/UnitLifecycleTripleRefusalT3.lean`) is the refusal refinement of one
Triple receive at related states, and `decrypt_ratchet_refines_complete`
(`Translation/UnitLifecycleDecryptRatchetCompleteT3.lean`) closes the path with it, under the same hypotheses and on the
same constants; nothing is assumed beyond what this section lists. The screen's run on that path
(`hypotheses_meet_open_path`) shows the model side only, as above.

**How the proof reaches the model loop.** `Model/Lifecycle.lean` keeps the fuel-indexed retry loop private. One lemma,
`receiveWithEvictionLoopResult_stop`, names it through Batteries' `open private` to prove that a retry refused for a reason
`fullStore` does not classify ends the loop; no model definition changes, and a public lemma in `Model/Lifecycle.lean`
would replace it under rule 7.

**Compiler trust.** The theorem, its complete form and the loop theorems rest on no compiler-evaluated constant. Until
2026-10-21 they rested on the nine of the Session unit's discharged Triple receive refinement (`CLAIMS.md`), and every
result composing that refinement, or the sparse ratchet's own, inherited some or all of them; those nine are kernel
proofs now. The number of compiler-trusted pinned results is the one `attest.py` reports (`counts.compiler_trusted`).

### The public `decrypt` on frames that are not initial messages: what it adds, and what it does not show

`decrypt_refines_ratchet_frame` (`Translation/UnitLifecycleDecryptT3.lean`; `CLAIMS.md`, the section on the public
`decrypt`) carries `decrypt_ratchet_refines_complete` through the pass-through arms of the generated `Session::decrypt`.
It assumes everything the previous section lists, with the same limits, and adds one premise.

**The scope premise.** `hframe` says that the model's reading of the message (`Model.Lifecycle.messageType`) is not an
initial message. It is a condition on the input bytes alone, decidable, and it selects no branch of the proof: the proof
derives the generated message type from it. It is not assumed of any message; a caller who wants the theorem for a
message must have it, and for an initial message the premise is false, so the theorem says nothing there.

**Not shown.** The repeated-initial branch of `Session::decrypt`: no claimed T3 theorem covers it (conditional branch
lemmas that take evidence records exist for its routes, in `Translation/UnitLifecycleT3.lean` and
`Translation/UnitLifecycleInitialDispatch.lean`, and are not claims); the model's comparison on that branch now decodes
both ephemerals and the translated comparison refines it (the next section), but no theorem composes it into
`Session::decrypt` on an initial frame. That a session the shipped
code produces meets the per-run hypotheses. One witness state passes `Session::invariant` (`UnitLifecycleDecryptT3.invReal`, the session of
`sessionOf_invariant`, whose identity keys on both sides are the public key of its own ratchet key), under the two
assumptions of "The headroom records" (`ValidKeyShape`, `OptionEqU64Shape`); it has no pending initial message, no receiving chain and no established ephemeral key, it is not shown to be produced by
`establish_initiator_for` or `establish_responder`, its message carries no agreement chunk, and the boundary records are
not discharged at it. The one run that reaches a success and clears a pending initial message (`pendReal`) does so on
the model side with the earlier screen's toy oracle, and on the generated side only under the boundary records at that
oracle, at a state that fails `Session::invariant` (`pendReal_fails_invariant`). The four runs of the earlier screens hold
empty associated data; for the refusal run,
`refReal_fails_invariant` proves that this fails `Session::invariant`. The theorem quantifies over the oracle; the model
frame lemma `decrypt_oracle_frame` (`tacenta-model/Model/LifecycleFrame.lean`) shows that `Model.Lifecycle.decrypt` reads
only the oracle's `draws`, `braidKem`, `dhPublic`, `dhAgree` and `aeadOpen`, so the fields the hypotheses leave unbound are
not read by the model's step; no theorem here applies the lemma.

**The run bounds from `Session::invariant`.** `decrypt_refines_ratchet_frame_of_counter_headroom` takes
`Session::invariant`, `CounterHeadroom` and `DecryptRatchetRunInputs` in place of `DecryptRatchetHeadroom` and
`DecryptRatchetRun`, as `decrypt_ratchet_refines_of_invariant` does for the private transaction (the previous section, "The
per-run bounds, from `Session::invariant`"). `CounterHeadroom` is assumed per run, with the exclusions "The headroom
records" lists: a session whose classical clock has parked, or whose sparse or Braid epoch or a chain counter has reached
its ceiling, is outside the corollary, permanently. `decrypt_frame_hypotheses_jointly_satisfiable` shows its hypotheses,
the boundary records included, together at the witness of `decrypt_of_invariant_hypotheses_jointly_satisfiable` under the
named laws `DecryptJointLaws`, with that witness's limits: built for the hypotheses, no agreement chunk, no ceiling
exercised away from zero, and a model step that refuses at the first agreement if the real agreement refuses the all-zero
key. `decrypt_refines_ratchet_frame_of_hypotheses` applies the corollary to that record with `hframe`, and
`decrypt_frame_at_invReal` carries the laws to the corollary's conclusion at that witness. No planted-fault control covers
these four results; their axiom and statement pins hold them.

**The random source.** As in the previous section, the source is read through a function of its value. For a source with
no state of its own, such as `OsRng`, `DecryptOracleOf.random32` and the draw field of `DecryptRatchetRun` cannot both
hold, so the theorem makes no claim about such a call. The argument outside Lean that the previous section records for
such a source is not proof.

**Compiler trust.** The theorem rests on no compiler-evaluated constant (until 2026-10-21 it rested on the same nine as
`decrypt_ratchet_refines_complete`, kernel proofs since); the `Session::invariant` corollary adds three opaque operations
that the invariant mentions and no compiler-evaluated constant; the corollary with the run bounds derived adds the same
three and no compiler-evaluated constant.

### The repeated-initial comparison: what it assumes, and what it leaves to the dispatch

`same_ephemeral_agreement_refines` (`Translation/UnitLifecycleInitialAgreementT3.lean`) says that the comparison
`Session::decrypt` makes between a repeated initial message's `ephemeral` and the session's `established_ephemeral` returns
the model's `sameEphemeralAgreement`, on every private key and every two byte strings.

**Assumed, about opaque operations.** Two records, neither proved of the real code. The agreement clause of the oracle,
`OracleOf.dhAgree` (the `dhAgree` field of `DecryptOracleOf`, the only field the theorem reads), says `PrivateKey::agree`
returns, at every key pair, the model oracle's `dhAgree` read through the byte views; nothing ties that oracle to X25519.
`DhCodecOf` says the byte views of the two opaque key types agree with `PrivateKey::from_bytes`,
`PublicKeyBytes::from_bytes` and `PublicKeyBytes::as_bytes` (as in "The `decrypt_ratchet` refinement", above). The translated
`decode_ec` needs neither: `session_decode_ec_refines` and `session_decode_ec_characterization`
(`Translation/SessionUnitDecodeEc.lean`) rest on the generated code and the model alone.

**What the model now says, and why it changed.** The model's comparison decodes both 33-byte strings with `DecodeEC`
(`Model.Lifecycle.decodeEc`) before agreeing, as session-establishment.md, Receiving the initial message, and the Rust do;
before, it agreed on the encodings, which `OracleOf` does not constrain (`encodedEphemeralAgreement_unconstrained`). The
decode-refusal arms are reached only on states the shipped readers do not produce: the initial-message decoder refuses a
re-spelled `ephemeral`, and clause (f) of `Session::invariant` refuses a session whose `established_ephemeral` does not
decode. That is read from the code; no theorem here states it.

**A disagreement with the page, recorded and not resolved.** `tacenta-spec/protocol/session-persistence.md` (Session,
Semantic rules, the optional fields' shape) says of `established_ephemeral` and the pending KEM ciphertext "Neither is
checked where it is used". For `established_ephemeral` that does not match the Rust, whose `same_ephemeral_agreement`
decodes it where it is used and returns `false` when it does not decode, or the model, which now does the same; the
page's "otherwise unavailable ... fails closed" supports the `false`. A spec sentence is the maintainer's decision, and
the page is unchanged (`GAP-REGISTER.md`, row `E2E-04-SAME-EPHEMERAL-MODEL`).

**The restated record field.** With the decode in the model, the inequality of `oracle.dhAgree` at the two 33-byte
strings that the `hagreementMismatch` field of `InitialDispatchBranchEvidence.ephemeralMismatch` and
`SessionDecryptEvidence.initialEphemeralMismatch` (and of `decrypt_initial_ephemeral_mismatch_refines`) asked for no
longer decides the model's verdict, so the field now states the verdict, `false`. No pin holds that field, and no
positive claim rests on it or on the records that carry it.

**Not proved.** The composition of `Session::decrypt` on an initial frame. The dispatch theorems of
`UnitLifecycleInitialDispatch.lean` still take caller-selected branch evidence (`InitialDispatchBranchEvidence`,
`SessionDecryptEvidence`), whose repeat premises `hmodelSame` and `hagreementMismatch` state the model's verdict on the
branch. `repeated_initial_agreement_true_iff` and `repeated_initial_agreement_false_iff` give each from the code's verdict,
but no theorem uses them in place of the premises, and `InitialDispatchBranchEvidence` still splits the route on byte
equality of the two ephemerals rather than on this verdict. Whether a state with an established ephemeral meets the other hypotheses of the
dispatch theorems is not checked here.

## The erasure coding's field is proved

`Model.Gf65536` implements GF(2^16), which the post-quantum agreement's chunking
is defined over. It is a proved field, not a probable one.

**Proved for every input.** The additive laws, commutativity, distributivity on
both sides, and associativity.

**Proved for every nonzero element.** That every nonzero element has the inverse
`inv` returns, all sixty-five thousand five hundred and thirty-five. This doubles
as a check on the reduction polynomial, since a reducible one would leave some
nonzero element a zero divisor with no inverse to return. The proof asks for more
than irreducibility: it needs two to have order exactly `size - 1`, so a
polynomial under which two has a smaller order is refused too. Until 2026-10-01
this was established by `native_decide`; it now follows, in the kernel, from that
order (a closed computation at `65535` and at each of its four maximal divisors),
so that the powers of two are the nonzero elements. Checked by substitution: with
the reducible `0x10001`, `gen_order` fails to build; with the irreducible
`0x1002B`, `0x1008D` or `0x103ED`, `gen_ne_21845`, `gen_ne_13107` or
`gen_ne_3855` fails.

The one thing still assumed is the reduction polynomial itself, which is ours
rather than the specification's: the published document fixes the field and not
which irreducible polynomial defines it, so it is wire-sensitive in the way the
derivation labels are, and is recorded in tacenta-spec/CONSTANTS.md.

The rule that governed the solver, while the laws were settled by `bv_decide`, is
worth carrying to any future work with one: **it settles statements mentioning
one product and none mentioning two.** The laws are now proved by the kernel
without a solver, and the same structure does the work:
`Model.Gf65536.linear_ext_w` -- a linear map is determined by its values on the
sixteen basis elements -- reduces a law about two maps that are linear in one
argument to sixteen closed cases, which the kernel evaluates.

## Not yet proven

- T1 (panic-freedom of the translated Rust of the core's verified zone via the
  Charon and Aeneas translation) **is proven**, under the stated assumptions and
  for the verified zone only, which is the eight proved leaf crates and, on
  the eight-leaf session unit, the lifecycle leaf's conditional T1 theorems, all
  conditional on records inhabited only in the sense of "The four contract records follow from an axiom base that has a model, under five laws" (three of them on a record that had a false field until it was restated; no T3 result)
  and not the product. The assumptions it rests on are not all ones anybody chose. Where
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
    put it outside the translated package and therefore opaque until
    the KDF change (ADR-0010): `hkdf_sha256` and `hmac_sha256` appeared in the generated Lean as axioms.
    Since then its bodies are a SHA-256, an HMAC and an HKDF in the subset Aeneas
    models, and `run-aeneas.sh` translates them into every unit that calls them
    (`--include-kdf`), so they are definitions there (`CLAIMS.md`, the section on
    `UnitLifecycleKdf`); the rest of this bullet is the history of the RustCrypto body. Inside the
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
    Four boundaries are, each a named hypothesis: `HmacTotal` and `HkdfTotal`
    for the key-derivation primitives, which were opaque by design until the KDF change (ADR-0010) (translated
    definitions since; the hypotheses stay, and `KdfLeafAgreements` proves them of this translation's KDF); `ZeroizingTotal`
    for the external `zeroize` crate, whose wrapper and projection cannot fail;
    `DerivedKeysModel`, the same crate's wrapper around the vector of derived
    keys (CR-15), which has to be a transparent container rather than merely
    total because the store loop reads a length back out of it, exactly as
    the session zone's `ZeroizingModel` does; and, in the revision of the classical ratchet this
    paragraph was written for, `VecRemoveTotal`, a gap in what Aeneas models rather than a choice
    (the translation no longer calls `Vec::remove`; see the entry below). The `zeroize` boundary is the reminder that every
    external crate on a proven path becomes an assumption whether or not
    anyone intended it.

    Second, **`receive` carries a precondition, and it is a real one.** The
    skipped-key store must be small enough that its length plus `MAX_SKIP`
    still fits a `usize`, measured at the largest the store can reach. Both
    platform widths admit it, since the constant part is 2000 plus 1000.

    This bound was wrong until 2026-09-10, and the way it was wrong is worth
    recording, because it is a failure mode this ledger exists to catch. It
    asked for the store's length plus the *whole* `u32` range. Aeneas models
    `usize` at the platform width, so on a 32-bit target `usize::MAX` and
    `u32::MAX` are the same number and the hypothesis said "the store holds at
    most zero keys" -- false of every state, the empty one included. It was not
    a demanding precondition. It was an impossible one, and a theorem with an
    impossible hypothesis is vacuously true, so `receive_no_panic` and the
    `receive` refinement established **nothing at all** on 32-bit targets,
    which the workspace compiles for (`armv7-linux-androideabi` in CI). The
    text here called it "a genuine constraint" and said a 32-bit caller was
    owed a check that no caller could ever meet.

    The bound is now `MAX_SKIP`, which is what the code actually needs:
    `skip_message_keys` returns `TooManySkipped` before the addition when the
    request is further ahead than `MAX_SKIP`, so the gap the store has to
    absorb is at most 1000 and never the counter's full range. The proofs use
    that guard (`T1.skip_gap_le`) instead of bounding the gap by the type.

    Where the state came from `State::from_bytes`, the precondition is
    discharged rather than assumed, and now entirely.
    `Translation/ImportInv.lean` proves that a state the translated
    `from_bytes` returns satisfies the crate's own `invariant()`, whose first
    clause caps the store at `MAX_SKIPPED_STORE`; what was left,
    `MAX_SKIPPED_STORE + MAX_SKIP ≤ usize::MAX`, is now proved outright at
    either width by `Ratchet.store_plus_skip_fits` instead of being passed in.
    `Ratchet.decoded_receive_no_panic` is therefore unconditional: the boundary
    assumptions, the bytes, and the decode. Nothing is owed by any caller on
    any target.

    Third, **the refinement of `receive` also assumes the store's clock has a
    step of room left, and that assumption stays with the caller even for a
    decoded state.** Skipped-key expiry counts received messages, and both the
    core's clock and the model's stop at `MAX_EVENTS = u32::MAX - 1`
    (`Model.State.ageStore`). The refinement was stated below that point when
    the model's clock did not stop, and still is: it says nothing at or past
    it, though the two now agree there. What the core does
    there is bounded rather than unspecified, and it is the opposite of
    expiring everything: `age_store` measures a key's age as
    `now.saturating_sub(stored_at)`, so once the clock has stopped no key's
    age grows any further, and a key stored fewer than `MAX_SKIPPED_AGE`
    events before the stop, or at any time after it, is never expired by age.
    Such keys stay in the store until the session's eviction (`evict_oldest`,
    driven when the store is full) removes them: retention, not loss, and no
    plaintext leaks. It is the same finite-width boundary the message counters
    already carry, and it is worth restating that a bound of this kind is not
    a formality: `receive` is the function an attacker drives.

    **The clock stops one below its ceiling, and that is where the assumption
    now bites.** `age_store` clamps the saturating step to
    `MAX_EVENTS = u32::MAX - 1` rather than letting it reach `u32::MAX`, so
    that `u32::MAX` is a value no run of this crate produces and the
    `invariant()`'s clock clause refuses only states the operations cannot
    build. `T3.receive_refines`'s `hroom` is therefore
    `events + 1 < u32::MAX`, not `events < u32::MAX`: at the parked value
    `events = MAX_EVENTS` the core held its clock still while the model's
    advanced. The model's clock now stops there too, so the two agree, but
    `hroom` is unchanged.

    For a state that came from `State::from_bytes`, the invariant gives
    `events < u32::MAX` -- `Ratchet.inv_gives_clock_room` in
    `Translation/ImportInv.lean` reads that clause back off it -- and that is
    **one step short of `hroom`**. The gap cannot be closed by strengthening
    the invariant: a parked clock is a state `age_store` produces and the
    decoder accepts, so a clause `events < MAX_EVENTS` would refuse a state
    the crate exports, which is the defect the clamp removed. So the step is
    taken as an explicit argument, `hclock_unparked`, on
    `Ratchet.decoded_receive_refines`, and it is a real restriction: it
    excludes exactly the one clock value an honest run comes to rest at, after
    2^32 accepted receives. Panic-freedom is unaffected --
    `Ratchet.decoded_receive_no_panic` takes no clock premise at all.

    How the decoder's refusal should be read turns on a property of the crate,
    not on anything proved here. If a run of the crate could leave the clock at
    `u32::MAX`, the refusal would be a **policy**: the decoder rejecting a
    state an honest run produced. If no run can, it is a **consistency
    check**: the decoder rejecting only states the operations cannot build.
    The clamp is what establishes the second, and it is an improvement over
    what this list carried before: `age_store` now *preserves* the invariant's
    clock clause rather than assuming it -- `events < u32::MAX` holds of the
    state it returns for any state at all -- so the value the clause excludes
    is one the operations never reach. That is still a property of the Rust
    and of the translated `age_store`'s clamp branch, argued in the comments
    beside the counter and in `tests/audit_import.rs` and
    `tests::the_clock_stops_one_below_its_ceiling`; **nothing in this tree
    proves it as a Lean theorem**, which would take a preservation theorem for
    `age_store`, and the reading above should be taken as resting on the crate
    rather than on the Lean. (The model's clock is proved to stay below
    `u32::MAX`, `Model.Ratchet.receive_events_lt`; that is a fact about the
    model, not about the translated `age_store`.) The store's "at most one entry per `(dh, n)`"
    premise (`hone`) comes off the same invariant
    (`Ratchet.inv_gives_store_is_map`).

- **Unmodelled standard-library operations are a recurring hazard.** Aeneas
  leaves several `core`/`alloc` operations as axioms, and each one that lands on
  a path we want to prove becomes an assumption rather than a theorem. The
  branch test compares arrays rather than `Option`s for that reason, since the
  translation models the array comparison and not the `Option` one. The one
  that remains is below, and should go the same way.

- **A trusted boundary that was not a deliberate one, replaced by a smaller one.**
  `Vec::remove` used to reach the generated Lean as an axiom, because Aeneas does not
  model it, and the skipped-key scan's proofs carried a stated hypothesis about it. The Rust no
  longer calls it: the removal helper (`remove_skipped_at`, in both ratchets) is a swap loop, a wipe
  of the removed entry and `Vec::pop`. The hypotheses the proofs now take about removal,
  `T1.RemoveSkippedAtTotal` (classical) and `SpqrT1.RemoveSkippedAtTotal` and
  `SpqrT3.RemoveSkippedAtAgrees` (sparse), are statements about those translated helpers, stated at an
  in-range index (`i.val < v.val.length →`, which every call site's `i < len` check supplies) and, for
  the classical and the agreement, naming the removed key and the erased-index result. They
  follow from named laws about the opaque constants the bodies reach (`LawPop`: `Vec::pop` of a
  non-empty vector returns the vector without its last element; the blanket and array `Zeroize`
  implementations return), proved in `SatisfiabilityRatchetLaws.lean`, `SatisfiabilitySpqrLaws.lean`
  and `UnitSatisfiabilityTripleLaws.lean`. Those laws are assumptions about standard-library and
  `zeroize` operations, tested against the real functions only by reading, so the trust moved from one
  statement about `Vec::remove` to them; the swap loop itself is proved and not assumed.

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

- **The removal hypotheses state the helper's value, and the length fact follows.** Under the
  index guard the classical `T1.RemoveSkippedAtTotal` states that the helper returns the removed
  entry's key and the list with that index erased; that a removal in range shortens the vector by
  exactly one -- which the purge scan needs, because it removes without advancing its index and so has
  nothing else to make its measure decrease -- follows from that value and is not assumed beside it.
  The sparse ratchet's `SpqrT1.RemoveSkippedAtTotal` states the length fact, and
  `SpqrT3.RemoveSkippedAtAgrees` names the removed element and the custom helper's erased-index
  result, since its refinement reads both. This is the recurring shape of the
  whole exercise: T1 needed only that an unmodelled operation returns, and
  refinement needs to know what it returned.

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
  agreement of the key-derivation primitives, the same boundary T1 rests on: in this
  translation it is a hypothesis of these theorems (about a translated definition since
  the KDF change (ADR-0010)), which `KdfLeafAgreements` proves of this translation's KDF and `UnitLifecycleKdf` of the
  Session unit's; that the model's KDF is the RFCs' is covered by vectors, not proof. It also excludes the cases
  where the Rust's `u32` counters and the model's `Nat` part company, which are
  real behaviours rather than gaps in the proof. The isolated-verified-zone
  translation it needs is in place, and it depends on the same Mathlib-backed
  Lean environment as T1. The vectors generated from the model give byte-level
  conformance evidence across the boundary it does not close.
- **The Braid's model states less than `tacenta-braid` checks, in tags 1 to 4,
  and both conform.** `session-persistence.md` requires the `header` and
  `ek_vector` inside a stored `key_pair` to pass the KEM split's validation,
  and scopes that clause to an implementation that knows the KEM key pair's
  layout. Where those two sit inside the field's 11,872 bytes is the KEM
  library's layout, which the page does not define and ADR-0006, point 5,
  delegates. `Model.PersistedState.BraidState` checks that field's length and
  accepts it, which is what the page asks of a reader outside the scope;
  `tacenta-braid` has the layout and checks the content as well. So this is no
  longer a gap between the model and the specification. What stays true, and
  is the reason this entry remains: the model does not state the clause, and
  `tacenta-braid` refuses stored states in those four tags that the model
  accepts.
  **No vector can pin the clause.** A stored state whose key pair fails it is
  refused by a reader inside the scope and accepted by one outside, and both
  are conforming, so no single verdict is right for every implementation. The
  part every implementation must apply, the field's length, is pinned
  (`key-pair-wrong-length`). The consequence is contained rather than hidden:
  no accepted vector in `braid-state.json` carries one of those tags,
  `runners/rust/tests/persistence.rs` asserts that, and the differential
  harness offers those tags only at a length both sides refuse. Every other
  rule of the Braid's stored format, and the whole of the triple ratchet
  state's, is modelled. The scoping is what closed the independent reader's
  `GAPS-5.md`, G5-02.

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

- `tacenta_braid`'s `mac_eq` is a hand-written comparison loop (see
  "Constant-time behaviour is assumed, not proven").
- A Rust test in `tacenta-core/braid` for the case in "The Braid's preservation theorems": a `HeaderSent`
  state whose `ct1` decoder is sized for 4097 bytes meets `ct1_bounded` and `decoders_bounded`,
  `Braid::invariant` rejects it, and the receive that completes the decoder returns a `ct1` of 4097
  bytes. It passed on a scratch tree. It is not committed because an edit under `tacenta-core/braid`
  changes the crate hash that `translation-attestation.json` records.
- The doc comment of `tacenta_spqr::State::invariant` (`spqr/src/lib.rs`) lists
  `hcb` and `hsb` as facts the invariant does not give and proposes reserving
  the top `EPOCHS_KEPT` epochs to close the gap. They follow from the invariant
  together with `hepoch` (`spqr_receive_premises` in
  `Translation/DecodedStateDischarge.lean`), so reserving them is not needed for
  those two premises (whether it would also remove `hepoch` has not been
  checked), and the text of `CLAIMS.md`, this file and `ImportInv.lean` says so.
  The comment's closing sentence, that the two are recorded as open in
  `CLAIMS.md`, is out of date too. The comment is not changed here: a
  comment-only edit inside a translated crate changes the crate's hash in
  `manifests/translation-attestation.json`, which only a Linux regeneration can
  refresh, so it waits for this window and is superseded by those texts until
  then.

One entry closed with this re-translation: `tacenta_spqr::State::to_bytes` and
`tacenta_braid::Braid::to_bytes` no longer grow their buffer by pushing, and
neither do the Triple's or the erasure coders'. The sparse `from_bytes` reader
also sizes its chain and skipped-key vectors from the checked counts before
copying secret-bearing entries. The remaining allocator caveat is the general
one stated above: these erasure measures are implementation hardening and are
outside the translated proof model.

Two further entries this list used to carry closed with the CR-03/CR-22
re-translation:

- `tacenta_braid::Auth::keys` and `Auth::from_root` are compiled only under
  `cfg(any(test, feature = "conformance"))` (CR-22), so a shipping build
  cannot plant or read a root key. They are no longer translated, and
  `BraidT1.lean` no longer carries `Auth.keys_no_panic`/`Auth.from_root_no_panic`.
- The Braid's two `epoch + 1` sites are now checked (CR-03): `checked_add`,
  answering `Failed` at `u64::MAX`, and `from_bytes` refuses a stored epoch
  of `u64::MAX` outright. `BraidT1.lean`'s `step_receive_no_panic`/
  `receive_no_panic` dropped their `hepoch` precondition as a result -- the
  ceiling is an outcome the theorems prove rather than a bound they assume.
  `BraidT3.lean`'s `step_receive_refines`/`Braid.receive_refines` keep it.
  They kept it because `Model.Braid` counted epochs in `Nat`, and its
  `epoch + 1` kept counting where the real code fails closed; the model now
  refuses the same steps (register item J-12), and whether the two theorems
  hold without `hepoch` has not been checked.

  Those two sites now also **reserve** `u64::MAX`: transitions (5) and (13)
  (`tacenta-spec/protocol/mlkem-braid.md`, "The state machine") refuse the
  step that would land on it rather than taking it, so what the
  transitions produce and what `read_epoch` accepts are the same set of
  states. That closes the last part of this entry that was only "in
  principle": `epoch < u64::MAX` is now a property of every state a run of the
  Braid reaches, where before it was a policy of the decoder over a ceiling
  `checked_add` at `u64::MAX - 1` would have yielded. It is still **not**
  derivable from the Braid's `invariant()`, which bounds the epoch only from
  below (`epoch >= 1`), and it is one step short of the refinement's `hepoch`,
  which is now `epoch + 1 < u64::MAX` -- the proofs use it to rule out the
  arm where, at `epoch = u64::MAX - 1`, the code and now the model answer
  `Failed` -- so `hepoch` stays a hypothesis of both T3 theorems and stays
  with the caller.

  The sparse ratchet's T1 has since followed the same path: `SpqrT1.lean`'s
  `advance_no_panic`, `maybe_advance_no_panic`, `send_no_panic` and
  `receive_no_panic` dropped `hepoch` and `hcounter`, the source's epoch and
  counter increments all being `checked_add` whose `None` arm returns
  `ChainExhausted`, and `SpqrT3.lean` keeps both. The model-side reason
  `BraidT3.lean` also had, a model counting in `Nat`, no longer applies to
  it: `Model.SparseRatchet` refuses at both ceilings, and whether the two
  bounds could now be dropped from `send_refines` and `receive_refines` has
  not been checked. Its `advance` reserves `u64::MAX`
  in the same way and for the same reason, and `SpqrT3`'s `hepoch` is
  likewise `epoch + 1 < u64::MAX`.

## Scope

**One-to-one sessions are implemented. Group messaging and multi-device are
not.** `tacenta-spec/protocol/group-messaging.md` and `multi-device.md` are
outline pages, `Model/MultiDevice.lean` is a stub, and there is no sender-key
implementation anywhere in the core.

Also not implemented, and listed here because a reader comparing this to
libsignal will look for them: persistent storage, platform bindings, and an
identity trust store are not in this crate at all. The crate classifies and
looks up a key against records the caller holds, and establishes an initiator
only under an expectation built from them (`sessions::identity`), but keeping
the records, and keeping them right, is the caller's (ASM-14). That is a much
easier interface to misuse than an address-keyed store that does it for
them.

**The post-quantum ratchet is in the session.** `Session` holds `triple:
tacenta_triple::State` and `braid: tacenta_braid::Braid` directly, rather
than a classical-only `ratchet::State`, and `encrypt`/`decrypt` drive both
halves as one transaction. So healing after a compromise does not rest on the
classical agreement alone.

What is *not* done for that integration is separate and open: proofs about
`Session::encrypt`/`Session::decrypt` themselves, the orchestration around
the crates. `UnitTripleT1.lean` and `UnitTripleT3.lean` cover the composition, on
the three-leaf unit; only
the session-layer orchestration remains uncovered.

Optional variants such as the Double Ratchet's header-encryption mode are out of
scope and recorded in the conformance manifest.

The distinction that matters: *implemented* is not *specified*
is not *proved*, and this document has to keep the three apart. An outline page
is not an implementation, and a passing test on an isolated crate is not a
feature of the library.
