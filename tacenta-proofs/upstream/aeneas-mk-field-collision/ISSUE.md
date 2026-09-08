# Issue filed with AeneasVerif/aeneas

**Filed as https://github.com/AeneasVerif/aeneas/issues/1231** on 2026-07-25,
labelled `bug`. The reproducer is public at
https://github.com/Natuvea/aeneas-mk-field-collision, where CI checks both
halves on every push: the control builds, the repro fails. That CI turning red
is the signal this has been fixed upstream and the workaround can be dropped.

The report text follows.

---

**Title:** A Rust struct field named `mk` collides with the generated Lean
constructor and breaks the whole file

**Body:**

A struct field named `mk` translates to a Lean structure field of the same name.
Lean already uses `mk` for a structure's auto-generated constructor, so the
projection is rejected and elaboration of the file fails.

The failure is not local to the struct. Because the structure no longer
elaborates, every later definition mentioning it degrades: the type is reported
as `Type ?u.3`, anything containing it (a `Vec` of it, a struct holding that
`Vec`) is pushed to `Type 1`, and the errors surface far away as universe
mismatches such as `Result.{0}` where `Result.{1}` is expected. Those downstream
errors are what surfaces first, and they point nowhere near the cause.

**Reproducer:** https://github.com/Natuvea/aeneas-mk-field-collision

The failing crate is nine lines with no dependencies:

```rust
pub struct S {
    pub mk: u32,
}

pub fn get(s: &S) -> u32 {
    s.mk
}
```

Translate it and build the generated Lean against the Aeneas Lean library:

```
charon cargo --preset=aeneas -- --package repro
aeneas -backend lean -dest . repro.llbc
lake build
```

The repository wraps that in `./check.sh repro` and `./check.sh control`, and
its CI runs both on every push, so the reproduction is checked rather than
asserted. CI passing means the control built and the repro failed with the
error below; it will start failing once this is fixed.

**Observed:**

```
error: Invalid field name `mk`: This is the name of the structure constructor
error: Invalid field notation: Field projection operates on types of the form
  `C ...` where C is a constant. The expression
  self
has type `S` which does not have the necessary form.
```

**Control:** the identical program with the field renamed to `key` translates
and builds cleanly, which isolates the field name as the trigger.

**Versions:** Aeneas `nightly-2026.07.22-b1214ca` (binaries and the Lean library
both from that release), Lean `v4.31.0`. Reproduced on macOS aarch64 and, in the
repository's CI, on Linux x86_64.

**Suggested fix:** escape or rename generated field names that collide with
Lean's reserved structure names, the way other name clashes are already handled.
`mk` is a plausible field name in cryptographic code, where it is the
conventional abbreviation for a message key.

**Workaround:** rename the field on the Rust side.
