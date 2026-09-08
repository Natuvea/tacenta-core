# Nested borrows: selecting a `&'static [u8]` constant by match

Filed as AeneasVerif/aeneas#1234 on 2026-07-27. Verified against Aeneas
`nightly-2026.07.22-b1214ca` on macOS and against the newest nightly on Linux.
Published with CI at `Natuvea/aeneas-nested-borrows-const-select`; the report
text is `ISSUE-BODY.md` beside this file.

## What happens

Selecting between two `&'static [u8]` constants with a `match` fails:

    [Error] Nested borrows are not supported yet
    [Warn ] Could not translate the body of function 'nested_borrows_const_select::repro because of previous error

`control` and `repro` in `src/lib.rs` are the same code over enums of one and
two variants. The output shows the difference:

    def control (p : One) : Result Std.Usize := do
      ok (Slice.len LEFT)

    def repro (p : Two) : Result Std.Usize := do
      sorry

## Why it is worth reporting beyond the unsupported feature itself

The one-variant case does not merely happen to work: the match is vacuous, so
Aeneas folds it and emits the constant directly. The construct therefore looks
supported for as long as the enum has one variant, and fails when a second is
added, which is the point at which such a parameter is usually introduced.

A parameter that selects a KDF `info` label by enum, so that labels can be
versioned rather than compiled in, has exactly this shape: it translates with
one variant, and every function that matches on it fails with the error above
once a second variant is added.

## What would help

In order of value:

1. **Support the construct.** Selecting a constant byte string by enum is an
   ordinary way to parameterise a key derivation, and a protocol that intends to
   negotiate labels has to do something equivalent.
2. **Failing that, report the fold.** If a match over a single-variant enum is
   folded away and the unfolded form would not be supported, saying so once,
   even as a note, would put the cost on the author rather than on a later
   reader.

## Reproducing

    cargo build
    charon cargo --preset=aeneas
    aeneas -backend lean -dest out nested_borrows_const_select.llbc

Exit status is 1 and `out/NestedBorrowsConstSelect.lean` contains one `sorry`.
