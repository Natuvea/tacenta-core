# Coverage-guided fuzzing

Six libFuzzer targets over every decoder and state machine that reads bytes
somebody else chose.

## The targets

| Target | Covers |
| --- | --- |
| `wire_decoders` | `message_type`, `decode_message`, `decode_initial`, `decode_bundle`, `decode_composite` |
| `protobuf_bodies` | `parse_prekey_body`, `parse_ratchet_body`, `decode_tag` |
| `persisted_state` | `from_bytes` on the ratchet, sparse ratchet, Braid, triple, and both erasure coders, plus `PrekeyStore::from_bytes` and `Session::import` |
| `session_receive` | `establish_responder` on an unauthenticated message, and `Session::decrypt` on both sides of an established session |
| `braid_receive` | `Braid::receive` and `commit` from either role, driven by a sequence of `Msg` values; every candidate that did not fail is adopted, so a transcript can carry the machine through all eleven live states, and the corpus is seeded with an honest transcript parked in each (`write_braid_receive_seeds` in `braid/src/tests.rs`) |
| `triple_receive` | `tacenta_triple::State::receive` and `commit` from either side, driven by a sequence of composite headers and agreement outputs (`write_triple_receive_seeds` in `triple/src/tests.rs`) |

The first three take bytes. The last three drive state machines, which is the
harder question: not whether parsing a message
panics, but whether a *sequence* of parsed-but-hostile messages walks a state
machine somewhere it cannot handle. Those three adopt whatever the machine
accepts: the property is that no accepted sequence panics, and a target that
never committed would fuzz only its starting state, which is what
`braid_receive` did before CR-10.

## What this is not

`tests/fuzz.rs` runs property tests with proptest at 2,048 cases per push. That
is not this, and the difference is not academic. Proptest generates from a
declared shape and cannot see which branches it reached, so it cannot search
toward the ones it has not. It does not generate a length field near
`u32::MAX` unless the declared shape pushes it there, and it does not notice a
run taking longer than it should. libFuzzer searches by coverage and reports a
slow unit within seconds.

The last point is the argument for this directory existing beside the proofs.
T1 says a function cannot panic; a loop that runs a declared count of
iterations is panic-free however large the count, and only a runtime search
sees the difference between a bounded and an effectively unbounded one.

## Running them

```sh
cargo fuzz run wire_decoders
```

Needs nightly Rust and `cargo install cargo-fuzz`. Each target keeps its corpus
in `corpus/<target>/`, which is committed: about 2,700 files and 11 MB in all.
It is the accumulated set of inputs that reached distinct branches, plus the
seeds the ignored tests named above write, and starting each run from it
rather than from nothing is most of what makes a short run worth anything: a
minute's run from an empty corpus reaches almost nothing a state machine
guards with a MAC, and a canonical persisted session or a MAC-valid Braid
header is not something mutation finds. The size is the price of that, paid
once, in files git stores compressed. Regenerate the seeds when a target's
layout or a persisted format changes; the rest is whatever the nightly run
merged back.

Findings land in `artifacts/<target>/` as `crash-*`, `slow-unit-*`, or `oom-*`.
Reproduce one with:

```sh
cargo fuzz run wire_decoders artifacts/wire_decoders/crash-<hash>
```

**A finding belongs in a unit test before it belongs in a fix**, pinned by
value in the crate's own tests, so whoever changes that decoder next has the
original input rather than a description of it.

## In CI

Two cadences, because "continuously" and "on every push" are different asks and
both matter:

- **`tooling/ci.sh`** runs each target briefly against the committed corpus
  when `cargo-fuzz` and a nightly toolchain are present. This is a regression
  gate, not a search: it catches a change that reintroduces a known input, and
  it is over in about a minute.
- **Nightly**, a nightly fuzz workflow runs each target for several minutes
  on a dedicated runner and uploads any artifact it finds. This is
  the search. A corpus that grows is the point, so the workflow commits back
  what it learns.

Neither is a substitute for the other, and neither is a substitute for the
proofs, nor the proofs for them: T1 says these functions cannot panic, and says
nothing about how long they run.
