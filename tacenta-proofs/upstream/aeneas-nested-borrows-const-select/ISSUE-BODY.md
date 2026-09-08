Selecting between two `&'static [u8]` constants with a `match` is rejected with "Nested borrows are not supported yet", and the enclosing function's body becomes `sorry`.

The unsupported construct is the smaller half of this report. The larger half is that the one-variant case does not fail, because the match is vacuous and gets folded away. The construct looks supported for as long as the enum has one variant, and breaks when a second is added.

Reproducer with CI: https://github.com/Natuvea/aeneas-nested-borrows-const-select

## Reproducer

`src/lib.rs`:

```rust
const LEFT: &[u8] = b"left";
const RIGHT: &[u8] = b"right";

pub enum One { Left }
pub enum Two { Left, Right }

/// Control: one variant, so the match folds. Translates.
pub fn control(p: One) -> usize {
    let s: &[u8] = match p {
        One::Left => LEFT,
    };
    s.len()
}

/// Repro: two variants, so the match must select. Body becomes `sorry`.
pub fn repro(p: Two) -> usize {
    let s: &[u8] = match p {
        Two::Left => LEFT,
        Two::Right => RIGHT,
    };
    s.len()
}
```

`Cargo.toml` is a bare `edition = "2021"` package with no dependencies.

```
cargo build
charon cargo --preset=aeneas
aeneas -backend lean -dest out nested_borrows_const_select.llbc
```

## Observed

```
[Error] Nested borrows are not supported yet
[Warn ] Could not translate the body of function 'nested_borrows_const_select::repro because of previous error
```

Exit status 1, and the emitted Lean shows the difference:

```lean
def control (p : One) : Result Std.Usize := do
  ok (Slice.len LEFT)

def repro (p : Two) : Result Std.Usize := do
  sorry
```

## Why the fold is the part worth reporting

The one-variant case does not merely happen to work. The match is vacuous, Aeneas folds it, and the constant is emitted directly. That gives a green result at exactly the moment such a parameter is usually introduced.

A parameter that selects a KDF `info` label by enum, so that labels can be versioned rather than compiled in, has exactly this shape: it translates with one variant, and every function that matches on it fails with the error above once a second variant is added.

## What would help, in order of value

1. Support the construct. Selecting a constant byte string by enum is an ordinary way to parameterise a key derivation, and any protocol that intends to negotiate labels has to do something equivalent.
2. Failing that, report the fold. If a match over a single-variant enum is folded away and the unfolded form would not be supported, saying so once, even as a note, would put the cost on the author rather than on a later reader.

## Environment

- Aeneas and Charon: `nightly-2026.07.22-b1214ca`
- Lean: `leanprover/lean4:v4.31.0`
- rustc: `1.96.0-nightly (562dee482 2026-03-21)`
- macOS aarch64, and ubuntu-latest x86_64 in the reproducer's CI
