# The label registry

Every application-chosen domain-separation string this library derives keys
with, in one place. Suffixes the published specifications state verbatim (the
Braid's four and the sparse ratchet's `Chain Start`) are recorded at tier
`fact` in `tacenta-spec/CONSTANTS.md` and are not repeated here.

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
here and are not a prefix of anything else in the table. All four are frozen
for the same reason the rest are. The specification-stated suffixes are named
otherwise (`AUTH_UPDATE`, `SCKA_KEY`, `EK_HEADER`, `CIPHERTEXT`, `CHAIN_START`)
and so fall outside the check, by design: their values are the specifications'
to fix, not this library's.

## Why they are not a shared module

The obvious implementation is one `labels` crate that everything imports. It is
rejected: these are seven independent leaf crates, each translated separately by
Charon and Aeneas precisely so that a construct one cannot express never reaches
another. A shared dependency would add an edge into every verified zone and put
the registry itself inside the translated surface, for no gain. The values are
constants, and a table checked mechanically against source binds them just as
tightly as a shared symbol would.

## Two spelling facts, frozen

**They are frozen because changing a label changes every key derived from it.**
Existing sessions would not resume, committed test vectors would all move, and
the change would not show up in any type. Neither affects security; both are
recorded here so that nobody normalises them later and breaks every derived
key doing so.

**1. ML-KEM-1024 is spelled two ways.** `tacenta-session` writes
`ML-KEM-1024`, matching the FIPS name. `tacenta-braid` and `tacenta-triple`
write `MLKEM1024`. Nothing derives from both, so the two never meet.

**2. `COMBINE_INFO` is a strict prefix of `SPLIT_INFO`.** The split label is the
combine label plus `:Split`.

The second is the one worth explaining. Distinctness is what a casual check
tests; it does not give you prefix-freedom, and prefix-freedom is the property
that matters when labels are adjacent to variable-length data. **Here they are
not.** Each is passed as HKDF's `info` argument in full, as a fixed constant,
never concatenated with anything an attacker influences, so the prefix relation
is not reachable as a collision. Recorded because it is the kind of thing that
stops being safe the moment someone builds a label at runtime.

## The scheme for new labels

New labels are not bound by the two facts above. They must:

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
labels are distinct, and that any *new* label is prefix-free. It does not verify
that a label is used where its name says it is, and it cannot: that is a claim
about the code's meaning, not its text.
