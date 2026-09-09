# The label registry

Every application-chosen domain-separation string this library derives keys
with, in one place. Suffixes the published specifications state verbatim are
recorded at tier `fact` in `tacenta-spec/CONSTANTS.md`; the Braid's four are
not repeated here, and the sparse ratchet's `Chain Start` is, for the reason
given under the table.

The labels are frozen: a single registry, checked mechanically against the
source, fixed before the protocol is frozen.

## The registry

| Crate | Constant | Value |
| --- | --- | --- |
| `tacenta-session` | `SK_INFO` | `Tacenta_CURVE25519_SHA-256_ML-KEM-1024` |
| `tacenta-ratchet` | `RK_INFO` | `Tacenta RK` |
| `tacenta-ratchet` | `MK_INFO` | `Tacenta MK` |
| `tacenta-spqr` | `PROTOCOL_INFO` | `Tacenta SPQR` |
| `tacenta-spqr` | `ROOT_LABEL` | `Root` |
| `tacenta-spqr` | `CHAIN_LABEL` | `Chain` |
| `tacenta-spqr` | `CHAIN_START_LABEL` | `Chain Start` |
| `tacenta-braid` | `PROTOCOL_INFO` | `Tacenta_MLKEM1024_SHA-256` |
| `tacenta-triple` | `COMBINE_INFO` | `Tacenta_CURVE25519_SHA-256_MLKEM1024` |
| `tacenta-triple` | `SPLIT_INFO` | `Tacenta_CURVE25519_SHA-256_MLKEM1024:Split` |
| `tacenta-core` | `APPLICATION_SIGNING_LABEL` | `tacenta:application-signature:v1\xff` |
| `tacenta-core` | `LAST_RESORT_HANDSHAKE_LABEL` | `tacenta last-resort handshake v1` |

`tooling/check-labels.sh`, which `tooling/ci.sh` runs, extracts these from source
and fails if
the source and this table disagree, so a new label cannot be added without being
registered here.

The check matches any `const` or `static` byte string whose name ends in
`INFO` or `LABEL`, `pub` or not, in every `.rs` file under `tacenta-core/src`
and under each leaf crate's `src`. That is what brings in the sparse ratchet's
two HMAC labels (`ROOT_LABEL`, `CHAIN_LABEL`: the domain-separation bytes its
root-key and chain-key steps are keyed with) and the root crate's two
(`APPLICATION_SIGNING_LABEL`, which prefixes a signing input, and
`LAST_RESORT_HANDSHAKE_LABEL`, which keys an HMAC fingerprint of public data)
alongside the HKDF `info` constants. `Root` and `Chain` are the shortest labels
here; `Root` is a prefix of nothing, and `Chain` is a prefix of `Chain Start`,
which is spelling fact 3 below. All four are frozen for the same reason the
rest are. The Braid's specification-stated suffixes are named otherwise
(`AUTH_UPDATE`, `SCKA_KEY`, `EK_HEADER`, `CIPHERTEXT`) and so fall outside the
check, by design: their values are the specification's to fix, not this
library's. The sparse ratchet's `Chain Start` is the one exception, named
`CHAIN_START_LABEL` so the check sees it: it is appended to the same
`PROTOCOL_INFO` as `CHAIN_LABEL`, with the same absent separator, and the two
are a genuine prefix pair, which is exactly what the check exists to notice.
Until CR-32 it escaped by naming, and a pair the check cannot see is not a
pair anybody has decided about.

## Why they are not a shared module

The obvious implementation is one `labels` crate that everything imports. It is
rejected: these are seven independent leaf crates, each translated separately by
Charon and Aeneas precisely so that a construct one cannot express never reaches
another. A shared dependency would add an edge into every verified zone and put
the registry itself inside the translated surface, for no gain. The values are
constants, and a table checked mechanically against source binds them just as
tightly as a shared symbol would.

## Four spelling facts, frozen

**They are frozen because changing a label changes every key derived from it.**
Existing sessions would not resume, committed test vectors would all move, and
the change would not show up in any type. None affects security; all are
recorded here so that nobody normalises them later and breaks every derived
key doing so.

**1. ML-KEM-1024 is spelled two ways.** `tacenta-session` writes
`ML-KEM-1024`, matching the FIPS name. `tacenta-braid` and `tacenta-triple`
write `MLKEM1024`. Nothing derives from both, so the two never meet.

**2. `COMBINE_INFO` is a strict prefix of `SPLIT_INFO`.** The split label is the
combine label plus `:Split`.

**3. `CHAIN_LABEL` is a strict prefix of `CHAIN_START_LABEL`.** `Chain` and
`Chain Start`, each appended to the sparse ratchet's `PROTOCOL_INFO`, so the
two complete `info` strings are `Tacenta SPQRChain` and
`Tacenta SPQRChain Start`. The first is a library label; the second is the
specification's initialisation suffix. `tooling/check-labels.sh` registers
this pair alongside the second.

**4. The sparse ratchet's suffixes have no separator; the Braid's do.** The
sparse ratchet writes `PROTOCOL_INFO || suffix` exactly as the published
pseudocode does, giving `Tacenta SPQRRoot`; the Braid's four suffixes each
carry a leading `:`, giving `Tacenta_MLKEM1024_SHA-256:ciphertext`. Two
conventions, each frozen, in two crates that share no derivation.

The second and third are the ones worth explaining. Distinctness is what a
casual check tests; it does not give you prefix-freedom, and prefix-freedom is
the property that matters when labels are adjacent to variable-length data.
**Here they are not.** Each is passed as HKDF's `info` argument in full, as a
fixed constant -- alone, or appended to a fixed `PROTOCOL_INFO` -- never
concatenated with anything an attacker influences, so neither prefix relation
is reachable as a collision. Recorded because it is the kind of thing that
stops being safe the moment someone builds a label at runtime.

## The scheme for new labels

New labels are not bound by the four facts above. They must:

- begin `Tacenta:`,
- use `:` as the only separator,
- name the protocol layer and the purpose, in that order,
- and be prefix-free against every label in the table, including each other.

`APPLICATION_SIGNING_LABEL` in `tacenta-core/src/sessions/mod.rs`
(`tacenta:application-signature:v1\xff`) already follows this shape and shows
the intent: a version segment, plus a terminator byte that cannot occur in the
prefix, which makes prefix-freedom structural rather than a property to check.

## What this does not cover

`tooling/check-labels.sh` checks that the source and this table agree, that the
labels are distinct, and that any *new* label is prefix-free against every
other, the two registered pairs excepted. It does not verify
that a label is used where its name says it is, and it cannot: that is a claim
about the code's meaning, not its text.
