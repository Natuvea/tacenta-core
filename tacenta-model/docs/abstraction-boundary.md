# Abstraction boundary

What the model computes concretely, what it holds at the trusted boundary, and
why the split is sound.

## What the model computes to exact bytes

The Double Ratchet's own contribution is its key schedule: how a root key, a
sequence of Diffie-Hellman outputs, and a message-delivery order determine the
chain keys and message keys, and how out-of-order delivery is absorbed. That
schedule is built entirely from one derivation family, HMAC-SHA256 and
HKDF-SHA256 over SHA-256. The model implements SHA-256 (`Model.Sha256`), HMAC,
and HKDF (`Model.Kdf`) from scratch, with no dependency, and anchors them to the
published known-answer values (NIST for SHA-256, RFC 4231 for HMAC, RFC 5869 for
HKDF) checked at build time. On top of them, `Model.State` and `Model.Ratchet`
compute the root keys, chain keys, message keys, and skipped-key store to exact
bytes.

The model is therefore a byte-exact oracle for the ratchet's key schedule and
state transitions. Given a root key, a script of Diffie-Hellman output bytes, and
a delivery order, it produces the exact message keys the implementation must
reproduce.

## What stays at the trusted boundary

Two primitives are not computed in the model:

- **Diffie-Hellman agreement (X25519).** The curve is a trusted-boundary
  primitive. The model consumes a DH output as an argument to a ratchet step
  (`dhRatchet` takes `DH(priv, peer_pub)` as bytes) rather than computing it.
  DH's own agreement is checked by the X25519 known-answer vectors in
  tacenta-test-vectors.
- **The AEAD (AES-256-CBC with HMAC-SHA256).** The model derives the AEAD
  material a message key expands into (`messageKeys` gives the encryption key,
  MAC key, and IV) and stops there. The cipher and MAC over the plaintext are the
  boundary primitive, checked by their own vectors.

So concrete ciphertext bytes are out of the model by design. The model asserts
the schedule and the state machine, which is exactly the part a curve-independent
or cipher-independent check should cover.

## Why the split is sound

- The boundary primitives are each independently checked against standard
  vectors, so holding them opaque in the model does not leave them unverified;
  it locates their verification elsewhere.
- A ratchet vector fixes the Diffie-Hellman outputs as explicit bytes, so the
  schedule is checked independently of which curve produced them. The
  implementation, given the same DH outputs, must produce the same keys. The
  self-consistency checks in `Model.Ratchet` exploit Diffie-Hellman symmetry,
  `DH(a, B) = DH(b, A)`, by handing both parties the same shared output, so the
  sender's message key and the receiver's recovered key coincide exactly.
- Freshness (new ratchet key pairs, new DH outputs) enters as caller-supplied
  arguments, so every model procedure is a pure, deterministic function of its
  inputs. That is what makes the model both an executable oracle and a subject
  the proofs can reason about.

## The derivation `info` labels

`KDF_RK` and message-key expansion take an application-specific `info` string
that the published specification leaves open. The model fixes its own labels
(`rkInfo`, `mkInfo`) so it is internally consistent and the core is checked
against it. The wire values a specific peer requires for interoperability are a
separate concern, pinned in the conformance manifest and determined under the
interoperability research boundary (see the decision records), never chosen by
reading another implementation.
