# Neutral adapter API

Every implementation under test sits behind an adapter exposing the same small,
behavioural interface. The harness drives it; each adapter translates between it
and one implementation. Tacenta does not reproduce libsignal's API, and this is
not libsignal's API: it is a Tacenta-defined surface, the minimum needed to
establish sessions and exchange messages. Interoperability claims against a
third-party peer are scoped to the bundle layer (ADR-0004); the message
operations serve the harness's own scenarios.

It is an **RPC** interface, not a library boundary (ADR-0005). The reference
adapter runs as a separate process or container, and the implementation team
sees these operations
and nothing of the adapter behind them.

## Operations

- `create_identity(seed) -> Identity`
  Create a long-term identity for a party. Returns an opaque handle the harness
  carries; its public part is observable through `export_public_state`. The
  `seed` is offered rather than imposed: an adapter that cannot pin its
  randomness ignores it, and the scenarios fall back to cross-decryption and
  property assertions.

- `generate_prekey_bundle(identity) -> PreKeyBundle`
  Produce a published bundle another party can use to start a session
  (identity public key, signed prekey and its signature, one-time prekey, and,
  where the implementation offers it, a post-quantum prekey). Opaque to the
  harness except as bytes to hand to `process_prekey_bundle`.

- `process_prekey_bundle(identity, bundle) -> Session`
  Establish an outbound session toward the owner of `bundle`. After this the
  party can `encrypt`.

- `encrypt(session, plaintext) -> Message`
  Produce a message (whatever the implementation emits, including any header)
  as opaque bytes.

- `decrypt(session, message) -> Result<plaintext>`
  Consume a message from the peer. Returns the plaintext or a predictable
  failure. A first inbound message may itself carry the material that
  establishes the inbound session.

- `send_message(session, plaintext) -> Message`
  Encrypt and hand the message to the harness for delivery. Distinct from
  `encrypt` because the harness controls delivery: it may hold, reorder,
  duplicate, or drop what `send_message` produced.

- `receive_message(session, message) -> Result<plaintext>`
  Accept a message the harness chose to deliver, in whatever order it chose.

- `reset_session(identity, peer) -> ()`
  Discard the session state for a peer, so the session-reset scenarios can
  observe how each implementation behaves when a session is re-established.

- `export_public_state(identity | session) -> PublicState`
  Return only externally observable state: public keys, message counters, and
  any values the interface already exposes. Never internal or private state.

## The bundle container

`generate_prekey_bundle` returns opaque bytes and `process_prekey_bundle` takes
them. The published protocol surface defines no bundle container: it fixes
canonical bytes per component and leaves composition to the application. So the
harness defines its own framing, purely so both adapters agree on how to
concatenate the components; it carries no protocol meaning. The concrete
byte-level profile is maintained with the harness, since it encodes
version-specific compatibility detail rather than anything about this
implementation.

## Rules

- **Adapters translate; they do not leak shape.** An adapter maps the neutral
  calls onto its implementation's public interface. It must not carry
  libsignal's identifiers, error strings, or data-structure shapes back into the
  neutral layer or into Tacenta (see `BOUNDARY.md`).

- **Controlled randomness where the interface permits it.** For known-input
  differential tests, feed both implementations identical keys and randomness
  where the public interface allows it, and compare. Where randomness cannot be
  controlled, fall back to cross-decryption and property assertions.

- **Do not require identical ciphertext.** Two correct implementations may use
  randomness differently, so equal ciphertext is not the interoperability
  criterion. The criterion is that each peer decrypts the other's output and
  that the asserted behavioural properties hold. Require byte equality only
  where an encoding must be canonical, and say which.

- **Opaque bytes across the boundary.** Messages, bundles, and public state
  cross the harness as bytes. The harness does not parse the peer's encoding; it
  hands bytes to the other adapter's `decrypt` / `process_prekey_bundle`.
