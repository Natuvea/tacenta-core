# Upstream findings

What has been established about the tools and libraries under this project by
using them, kept here rather than in commit messages because most of it took
hours to establish and none of it is written down anywhere else. Mostly the
translation toolchain, Charon and Aeneas, and one dependency finding at the end.

One rule for this file: **every claim names the evidence that establishes it.**

Pinned toolchain: `nightly-2026.07.22-b1214ca`. Findings are against that unless
stated.

## Filed

### `mk` field collision, filed as AeneasVerif/aeneas#1231

A Rust struct field named `mk` collides with Lean's generated constructor and
breaks elaboration of the whole file, surfacing as universe errors far from the
cause. Reproducer in `aeneas-mk-field-collision/`, public at
`Natuvea/aeneas-mk-field-collision` with CI on both halves. That CI going red
means it is fixed upstream.

### Nested borrows, filed as AeneasVerif/aeneas#1234

`aeneas-nested-borrows-const-select/`, with `ISSUE.md` and the report text in
`ISSUE-BODY.md`. Public with CI at `Natuvea/aeneas-nested-borrows-const-select`.
Selecting a `&'static [u8]` constant by match is rejected with "Nested borrows
are not supported yet".

Two jobs there, both asserting each half. `pinned` holds the toolchain at the
release the report names, so the report stays reproducible. `latest` tracks the
newest nightly, and is the one that turns red when the construct is supported.
Both were green at publication, which is the state that means the bug is still
there.

The part worth reporting is not the unsupported feature. It is that a
single-variant enum makes the match vacuous, so Aeneas folds it and the code
translates; the error appears only when a second variant is added. A
translation test therefore has to exercise the shape a parameter is intended to
take, not the shape it has on the day it is introduced. See "Findings" below.

## Not bugs, but worth knowing

### The output is ANSI-coloured and full of progress escapes even when redirected

`/tmp/*.log` captures from a non-tty contain `[?25l`, `⠋`, and colour codes.
There is a `-color` flag documented as "Use colors when printing log messages",
which reads as opt-in; colour appears without it.

Greps over redirected output can therefore match nothing. Strip with
`sed 's/\x1b\[[0-9;]*m//g'` before matching, or better, **use the exit code and
do not parse the output at all**.

A `-no-progress` flag, or honouring tty detection, would make redirected
output plain.

### A failed run still writes the partial file, at the destination path

Aeneas exits **non-zero** and announces `Generated the partial file (because of
N errors)`, which is honest. But the partial file lands where the good one goes.
Nothing about the file on disk says it is partial except the `sorry` inside it.

A `-no-partial-file`, or a distinct output path for partials, would let a script
distinguish the two without reading the contents. We work around it by refusing
to stage any generated file containing `sorry`
(`tacenta-proofs/scripts/run-aeneas.sh`).

### `Drop` is not translated

Adding `#[derive(Zeroize, ZeroizeOnDrop)]` to the ratchet's `State` and
`SkippedKey` produces a **byte-identical** `TacentaRatchet.lean`. The erasing
destructor is real in Rust and absent from the translation.

That is defensible, since `Drop` is not part of the functional behaviour
Aeneas models. But for cryptographic code it is worth knowing loudly. Key erasure is
exactly the kind of property someone would assume a proof covers. T1 and T3 say
nothing about it, and nothing in the output says so either. It is recorded in
`tacenta-spec/protocol/key-deletion.md` instead.

## Findings

### Aeneas exits 1 on a body it cannot translate, 2 with `-abort-on-error`

Measured against the pinned toolchain. `run-aeneas.sh` runs under `set -eu`, so
a failing Aeneas stops the script before the staging step, and the previously
staged translation remains on disk. A local `lake build` after a failed run is
therefore a build against the last translation that was staged, not against
the code just changed; confirm the staged file changed before relying on one.
CI is not exposed to this, because it regenerates from a fresh checkout (the
verification workflow, which also runs nightly on cron).

The rule generalises past this tool: **when a step fails, ask what the previous
step's output is still doing on disk.**

### A function returning `&'static [u8]` translates

Tested by adding such a function to the ratchet and calling it from `kdf_rk`:
translated cleanly, and the generated Lean was byte-identical to the version
without it. The unsupported construct is the nested borrow in a multi-variant
`match`, above, and with a single-variant enum every form of that code folds to
the same thing, so moving the `match` between functions changes nothing. A
translation test has to **exercise the shape you intend to use, not the shape
you have today**: a test over a two-variant enum is what distinguishes the two
cases.

## Things that are true and worth knowing

- **Charon's cargo invocation rebuilds on a source edit.** Verified by
  timestamp: the `.llbc` is written a second after the source edit, and charon
  reports `Compiling`. No freshness cache serves an old one.
- **`-abort-on-error` exists** and exits 2. We do not use it: we want the partial
  file for diagnosis, and the plain exit code already suffices.
- **The trusted boundary has to be a separate crate.** Inlining the key
  derivation pulled RustCrypto's trait hierarchy into the generated Lean and
  produced 57,272 lines that would not build. `tacenta-core/kdf` exists for this.
- **`?` does not translate.** It desugars through `Try` into universe-polymorphic
  Lean that will not typecheck. The crate carries
  `#![allow(clippy::question_mark)]` because the lint demands the breaking form.

## Dependencies

### libcrux-ml-kem 0.0.10: `incremental` and `std` are mutually exclusive

`std` implies libcrux's `rand` feature, and the `rand`-gated code inside the
incremental interface is written against `rand 0.9` while the crate depends on
`rand 0.10`. So asking for `std` and `incremental` together fails to compile,
with an error that names `rand`, which nobody asked for. Reproducer and write-up
in `libcrux-incremental-rand/`, verified to fail and verified that dropping
`std` fixes it.

Cargo unifies features across a graph, so one crate enabling `incremental`
turns it on for every consumer of `libcrux-ml-kem`. That on its own costs
nothing: only `std` compiles the affected module, so the failure follows
whichever consumer asks for `std`, regardless of which other dependencies are
in the graph. The test that settles a question like this is building each
dependency alone with the same features, and it costs one minute.
