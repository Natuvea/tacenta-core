# Security policy

## Reporting a vulnerability

Email **security@natuvea.com**. Please do not open a public issue for a
security report.

If you would like to encrypt the report, ask for a key in a first message with
no details in it.

**What to include.** The affected crate and revision, what an attacker gains,
and the smallest thing that demonstrates it. A failing test, a byte string, or
a Lean snippet is worth more than a paragraph.

**What to expect.** Acknowledgement within three working days, an assessment
within ten, and a disclosure timeline agreed with you rather than imposed. You
will be credited unless you ask not to be.

## Authorisation and safe harbour

We authorise you to obtain, build and test the published code, and to test only
systems expressly identified as in scope, solely for good-faith security
research conducted in accordance with this policy. To the extent we have legal
authority, we will not bring or support civil claims, or request criminal
investigation, solely in respect of activity covered by this authorisation. If
a third party takes action concerning authorised activity, we will make clear
that we authorised it.

**Good-faith security research** means testing intended to improve security,
carried out no further than reasonably necessary to demonstrate a
vulnerability, while avoiding harm, service disruption, privacy violations and
unnecessary access, retention or disclosure of data. If you encounter sensitive
data, stop, secure it and notify us promptly. Extortion, social engineering,
physical intrusion, denial-of-service testing and testing third-party systems
are not authorised.

An accidental, non-material departure from this policy will not by itself
remove this safe harbour if you stop, notify us promptly and take reasonable
steps to prevent or remedy harm. This authorisation applies only to assets we
own or are authorised to place in scope. It does not bind third parties or
public authorities, and is subject to any disclosure required by law.

## Read this before you start

This is a **research implementation of a cryptographic protocol**, not a
production library. Every crate is `0.0.0` and `publish = false`, there is no
supported-version policy, and **it has not been independently audited**.

**This is not a standalone production library.** It reaches production only as
the pinned core inside the Tacenta SDK, behind that product's own review and
release process. Do not adopt these crates directly for production on the
strength of this repository alone; if you found them deployed that way, that
itself is a report we want.

## What is in scope

- The primitives, and their composition: X25519, HKDF/HMAC-SHA256, the
  AES-CBC + HMAC AEAD, ML-KEM-1024, Ed25519 and **XEdDSA in particular**, which
  is our custom implementation and the deliberate exception to using vetted
  code.
- PQXDH session establishment, the Double and Triple Ratchets, the sparse
  post-quantum ratchet, the braid, and erasure coding.
- Every decoder. They parse attacker-controlled bytes and the panic-freedom
  proofs are about the Aeneas model of that Rust, not the machine code.
- **The proofs themselves**, in two distinct senses, and both are welcome:
  a theorem that does not say what its name and docstring claim, and a claim in
  `CLAIMS.md` that the theorems do not support.

## The trusted boundary

Named rather than hidden, so a finding against it is a finding against a
documented assumption rather than a surprise. `tacenta-proofs/LIMITATIONS.md`
is the full statement; in short, the Lean kernel, the Charon and Aeneas
translation, the Rust compiler, the primitive crates, and constant-time
behaviour are all trusted rather than established here.

A demonstration that one of those assumptions is *false for this code* is among
the most valuable things you could send us: an opaque operation that is not
total, a translation that does not match the Rust, or a KDF disagreement that a
refinement theorem assumes away.

## Known open issues

Published so a reporter does not spend time rediscovering them:

- **XEdDSA has no published known-answer vectors.**
- **The composite decoder is canonical by construction and by test, not by
  proof**.
- **The decoders have no 32-bit runtime regression test**; `tooling/ci.sh`
  cross-compiles for `armv7-linux-androideabi` when that target is installed
  and executes no 32-bit code.

## Third-party material boundary

This public tree contains no libsignal implementation source, compiled objects,
reference-adapter implementation, research transcripts, or libsignal-derived
fixtures. **Please do not send those materials in a vulnerability report.**
Describe the externally observable behaviour and provide independently generated
inputs where possible. ADR-0003 and ADR-0005 state the engineering policy for
handling third-party material; libsignal's source code is not an input to this
project.
