# Session L4 Phase 0 translation spike — 2026-09-18

## Status and scope

Disposable maintainer-side experiment, not an assurance result. The scratch
tree was based on `639c1d8`, whose production source is identical to main
`abd0c3b`; `639c1d8` adds only the three proposed Session L4 decision records.
No generated file or scratch crate from this experiment is proposed for
shipping.

The experiment answers two questions from Phase 0 of the session end-to-end
proof plan:

1. Does a separate primitive dependency remain opaque when Charon translates
   a lifecycle leaf selected with `--package`?
2. How far does the actual, unrevised lifecycle source get through the pinned
   Charon/Aeneas pipeline after a mechanical crate carve-out?

The local binaries were `/Users/natuvea/tools/aeneas-nightly/{charon,aeneas}`.
Their SHA-256 values were:

```text
f52e833d52ef4cab8bd6a321cc2d64f51aaaf8e51055ca45910d6b1b1d07ce2e  charon
785647c96989b38b80450c5349771ae3ace9961ce4bf7eaae1e552a2c7f90c78  aeneas
```

The generated Lean imports the repository's pinned Aeneas library commit
`b1214ca0a024e8121f41fe2b2ed15e26af02373b`. This macOS experiment does not
replace the pinned Linux regeneration required for evidence.

## Primitive-boundary probe

The scratch tree copied the four existing primitive implementations into a
`tacenta-boundary` dependency and exposed the nine functions proposed in
`SESSION-L4-PRIMITIVE-BOUNDARY-DECISION.md`. A small lifecycle probe called
all nine.

Commands:

```text
cargo check -p tacenta-boundary -p tacenta-lifecycle-spike
charon cargo --preset=aeneas -- --package tacenta-lifecycle-spike
aeneas -backend lean -dest <scratch> tacenta_lifecycle_spike.llbc
lake env lean <scratch>/TacentaLifecycleSpike.lean
```

Result: all commands passed. The generated file was 234 lines. It contained
one opaque Lean axiom for each of `dh_public`, `dh_agree`, `aead_seal`,
`aead_open`, `kem_encapsulate`, `kem_decapsulate`, `xeddsa_verify`,
`xeddsa_sign` and `random32`. The lifecycle probe's four functions were
transparent. No primitive function body was translated. The public
`kem::KemError` and `kem::KeyPair` type declarations crossed the boundary, as
their use in signatures requires.

This supports D2's package-boundary premise. It does not establish any of the
nine future contracts.

## Shipping-shaped lifecycle probe

The scratch tree then made a second leaf from the real, unedited
`sessions/mod.rs`, `sessions/lifecycle.rs`, `serialization/mod.rs` and
`serialization/composite.rs`. Its dependencies were the existing leaf crates
and the scratch primitive boundary. The top-level crate was not changed to use
it.

Results:

- `cargo check -p tacenta-lifecycle-full-spike`: passed.
- Charon extraction of `tacenta-lifecycle-full-spike`: passed.
- Aeneas emitted a partial 8,233-line Lean file with 10 `sorry` bodies. It
  reported 28 errors in 12 distinct classes.

The distinct blockers observed were:

- early returns inside loops in `PrekeyStore::replenish` and
  `Session::decrypt_ratchet`;
- returns inside nested loops in `PrekeyStore::from_bytes` and
  `PrekeyStore::invariant`;
- a higher-ranked-lifetime failure reached through iterator `find` in the
  store lookup/publication helpers;
- closure/borrow failures in `signatures_verify`, `peek_one_time_kem` and
  `establish_responder`;
- Aeneas interpreter errors in `PrekeyStore::publish`,
  `publish_one_time_batch`, `to_bytes` and two small store helpers;
- a slice-pattern interpreter error in `serialization::message_type`;
- a context error at the final store mutation in `establish_responder`;
- generated-name clashes for the `Error::Handshake`, `Error::Decode` and
  `Error::Triple` variants. Inspection of the partial Lean showed that
  higher-order constructor uses such as `map_err(Error::Handshake)` caused
  Aeneas to emit wrapper functions with the constructor names; explicit
  `match` expressions remove the wrappers without renaming the public Rust
  variants.

The partial full-leaf translation exposed 18 primitive method/function axioms
rather than the proposed nine-function surface because the mechanically moved
source still called the old primitive modules directly. Rewiring those calls
to the nine functions is required before the opaque-assumption budget can be
measured.

## Follow-up rewrite and rooted-translation measurement

A disposable follow-up applied behavior-preserving source-shape rewrites to
the copied leaf and retained all 60 copied unit tests passing (two fixture
printers ignored). This is still experiment evidence, not proposed shipping
source. Among the rewrites were explicit constructor matches, total loop
accumulators, proof-sized responder-selection helpers, explicit byte indexing,
and replacing `usize::max(1)` with the equivalent comparison. The last rewrite
matters because Aeneas accepted `Ord::max`, but the emitted Lean applied the
trait instance where a comparison function was expected; only the Lean kernel
check exposed it.

Translating the entire package is not an acceptable production shape. Charon
emitted an approximately 10 GiB LLBC file. A sequential Aeneas run cleared all
410 prepasses and began translating bodies, but the process reached an
approximately 157 GiB macOS-reported footprint while expanding the store
decoder and was stopped after about 30 minutes. Before it was stopped it had
reported two remaining body failures: a KEM selection loop and two `for` loops
in `PrekeyStore::to_bytes`. Both were subsequently rewritten and passed when
measured through smaller call-graph roots.

Charon's `--start-from` option made the useful unit visible. Disposable free
functions rooted inherent methods that Charon cannot name directly. Each row
below passed Charon, Aeneas with zero errors and zero generated `sorry`, and
`lake env lean` against the pinned Aeneas Lean library:

| Root | LLBC size |
| --- | ---: |
| `establish_initiator_for` | 2.0 MiB |
| `establish_responder` | 4.5 MiB |
| `Session::encrypt` | 1.3 MiB |
| `Session::decrypt` | 2.3 MiB |
| `Session::export` | 1.7 MiB |
| `Session::import` | 7.2 MiB |
| `PrekeyStore::to_bytes` | 4.7 MiB |
| `PrekeyStore::from_bytes` | 13 MiB |

`PrekeyStore::from_bytes` was initially the isolated blocker. Its call-graph
root still emitted approximately 10 GiB after replacing the two `HashSet`
checks with small prefix-search helpers. Splitting the decoder into head,
replay-record and retired-prekey helpers reduced that root to 13 MiB; it then
passed Aeneas with zero generated `sorry` and passed the Lean kernel. The
growth therefore belonged to the decoder's structured control flow rather
than merely to translating the hash-table dependency. Production Phase 0 must
retain that split.

This measurement changes the proposed translation layout: the pinned command
should use an explicit, reviewed list of public call-graph roots (with tiny
free roots for inherent methods), and CI must verify that the list covers the
shipping lifecycle API. Translating `crate` is both wasteful and unsafe for the
runner. The coverage gate is part of the change, because a missing root would
otherwise silently omit shipping code.

## Decision impact

- **D1 remains viable.** The real lifecycle and serialization source compiles
  and Charon extracts when mechanically placed in a shipping-shaped leaf.
- **D2's opacity premise holds.** A package dependency's function bodies did
  not enter the lifecycle translation.
- **D7 needs a wider implementation inventory.** The eviction loop is not the
  only structural rewrite. Tier-4 store and codec bodies also block a complete
  translation. Calling them "translated but unproved" still requires Aeneas
  to translate their bodies without `sorry`.
- **The translation must be rooted and coverage-gated.** Eight central roots
  now translate and kernel-check independently in seconds, including the
  split store decoder. The all-items run exhausted a practical resource budget.
- The production Phase 0 work should first rewire the primitive surface and
  remove the name clashes, then address loop/iterator/closure failures in
  dependency order. It must rerun Aeneas after each class because one ignored
  body can hide failures behind it.
- If the Tier-4 rewrites become semantic or disproportionately large, reopen
  D1 and evaluate a concrete store module boundary. Do not make the store
  opaque merely to obtain a green translation: responder store effects are in
  the accepted theorem surface.

## Reproduction limit

The scratch crates and partial Lean files were intentionally not committed.
This record contains the commands, inputs, binary hashes, counts and observed
failure classes needed to repeat the experiment. A production change must
reproduce it from committed source with the pinned Linux toolchain and normal
attestation flow.
