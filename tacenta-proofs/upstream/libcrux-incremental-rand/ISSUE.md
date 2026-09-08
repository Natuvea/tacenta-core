# libcrux-ml-kem 0.0.10: `incremental` + `std` does not compile against rand 0.10

## Summary

Enabling `libcrux-ml-kem`'s `incremental` feature together with `std` fails to
compile. `std` implies the `rand` feature, and the `rand`-gated code in the
incremental interface uses `rand::TryRngCore` and `rand::RngCore` at the crate
root, which the `rand 0.10` the crate itself depends on does not export.

The crate's own manifest declares `rand = "0.10"`, so this is not a
version-selection problem on the consumer's side. The default resolution is the
one that fails.

## Reproducer

`Cargo.toml`:

```toml
[package]
name = "libcrux-incremental-rand"
version = "0.0.0"
edition = "2021"

[dependencies]
libcrux-ml-kem = { version = "0.0.10", default-features = false, features = ["mlkem1024", "std", "incremental"] }
```

with an empty `src/lib.rs`. `cargo build` gives:

```
error[E0432]: unresolved import `rand::RngCore`
   --> libcrux-ml-kem-0.0.10/src/mlkem.rs:161:33
    |
161 |         use ::rand::{CryptoRng, RngCore};
    |                                 ^^^^^^^ no `RngCore` in the root
   ::: libcrux-ml-kem-0.0.10/src/mlkem1024.rs:704:5
    |
704 |     impl_incr_key_size!();
    |     --------------------- in this macro invocation

error[E0432]: unresolved import `rand::TryRngCore`
   --> libcrux-ml-kem-0.0.10/src/mlkem.rs:372:17
    |
372 |             use ::rand::TryRngCore;
    |                 ^^^^^^^^^^^^^^^^^^ no `TryRngCore` in the root
```

Dropping either `std` or `incremental` compiles. Adding `rand` explicitly does
not help, because `std` had already enabled it.

## Cause

Both sites are inside `#[cfg(feature = "rand")]` blocks in `src/mlkem.rs`,
expanded per parameter set by `impl_incr_key_size!`. They are written against
`rand 0.9`, where `TryRngCore` lives at the crate root; `rand 0.10` moved it.

`incremental` itself is fine. What fails is the intersection of `incremental`
and `rand`, and that intersection is hard to see from outside, because `std`
enables `rand` implicitly:

```
std  ->  rand  ->  dep:rand
```

So a consumer who never asked for randomness gets the module that does not
compile, and the error names `rand` rather than the feature they actually set.

## Why we noticed

The ML-KEM Braid needs exactly this interface: `Encaps1` from the encapsulation
key header alone, `Encaps2` from the rest. Nothing else in the protocol needs
`incremental`, and nothing else in libcrux offers that split.

## Workaround

Do not enable `std` on `libcrux-ml-kem`. `alloc` covers what we need, and
`incremental` then compiles.

## Status

Not yet filed. Against `libcrux-ml-kem 0.0.10` and `rand 0.10.2`.
