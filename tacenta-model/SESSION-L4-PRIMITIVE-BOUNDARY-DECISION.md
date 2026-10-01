# Session L4 primitive boundary decision

## Status

Proposed for rule-7 review.

Recorded 2026-09-18 against `tacenta-core` main `abd0c3b`.

## Context

The session orchestration calls X25519, AEAD, ML-KEM, XEdDSA and randomness.
Their production implementations use dependencies that are outside the pinned
Charon/Aeneas translation surface. The session refinement must still expose
the complete arguments and results of every such call; otherwise, for
example, a Rust encryption under the wrong key could agree with a model which
encrypts under the intended key.

## Decision

Create a shipping crate named `tacenta-boundary` containing the existing
production implementations. Keep its public `PrivateKey`, `PublicKeyBytes`
and `KeyPair` types at the boundary: moving their representation into the
lifecycle leaf would either expose primitive internals to translation or
change the existing public API.

The complete Phase 0 translation determines the opaque call surface rather
than an anticipated wrapper list. For the five proof roots (`encrypt`,
`decrypt`, initiator and responder establishment, and session import), that
surface is covered by these ten named contracts:

1. `DhCodecTotal`: construction, public derivation, byte projection,
   persistence projection and public-key equality;
2. `DhAgreeTotal`;
3. `AeadSealTotal`;
4. `AeadOpenTotal`;
5. `KemEncapsulateTotal`;
6. `KemDecapsulateTotal`;
7. `KemCiphertextLenTotal`;
8. `XeddsaVerifyTotal`;
9. `XeddsaSignTotal`; and
10. `Random32Total`, over the lifecycle's fixed-width use of `RngCore`.

`DhCodecTotal` groups operations over the same two opaque DH types so their
non-vacuity is witnessed jointly; separate witnesses would not show that all
of the contracts can hold in one interpretation. The other contracts each
cover one opaque call. The proposal requires every contract to have a concrete
non-vacuity witness in the session unit's satisfiability module and a
corresponding entry in `LIMITATIONS.md`;
returning `None` or `Err` is an ordinary result of a
boundary call and is not assumed away.

The executable lifecycle model represents every boundary operation as a
function of its complete argument list. Randomness is an ordered draw trace:
each call consumes the head and returns the remaining trace. `OracleOf`
relates each concrete boundary call to the matching model call and relates
the concrete RNG interaction to that ordered trace.

XEdDSA signing is included even though prekey publication is outside the five
proof roots. `Identity::sign`, `sign_message` and the store publication and
rotation methods move with the lifecycle leaf, so the translation and its
audit still encounter that opaque call.

## Assumption budget

Note, 2026-09-20: the complete translation and its T1 layer required twelve
contracts, the cap: the nine above less `AeadSealTotal`, plus `AeadSealBounded`
(the AEAD call returns ciphertext plus its 32-byte authentication tag at most
forty-eight bytes longer than the plaintext, which the framing headroom needs),
`VecPopTotal` and
`MessageKeyMaterialRoundTrip` over standard-library and `zeroize` operations
Aeneas leaves opaque. `LIMITATIONS.md` and `UnitSatisfiabilitySession.lean`
(`all_twelve_contracts_satisfiable`) carry the twelve.

Note, 2026-09-29: the identity-key rule (identities-and-devices.md, Identity
keys) makes the lifecycle call one more boundary operation,
`tacenta_boundary.dh.is_prime_order_public`, from `verify_bundle` and
`responder_shared_secret` and so from the establishment roots. It gets its own
contract, `DhIdentityTotal` (the call returns for every key), a thirteenth, and
this note reopens the cap and recuts it at thirteen. The contract is kept apart
from `DhCodecTotal` so that the codec's joint witness and its projections do
not change; its own witness (`dh_identity_satisfiable`) interprets the key type
by itself, and the coverage theorem now carries thirteen names
(`all_thirteen_contracts_satisfiable`, renamed from the twelve-name theorem
above). Nothing in Lean says what the predicate computes: the contract is
totality only. What it computes is stated by `Model.IdentityKey.valid`, written
from the page, and pinned by the identity-key vectors and by the differential;
the refinement contract binds the model's `identityValid` oracle to the
translated `is_valid_identity_key`.

Note, 2026-10-01: the repair of the receive decoder hypothesis (#217) gave
`EstablishResponderContracts` a field, `divCeilValue`: the value `(a + 31) / 32`
of the opaque `usize::div_ceil` at divisor 32. `establish_responder_no_panic`
takes it and uses it once, to bound the decoder a freshly built responder Braid
holds. It is an assumption about a standard-library operation that Aeneas leaves
opaque, as `VecPopTotal` is, and `establish_responder_no_panic` takes it through
`EstablishResponderContracts`. Fields about other opaque operations that the
records inherit from the leaf proofs, such as `RangeFullIndexTotal`, are not
counted by this decision. `divCeilValue` is not inherited: no earlier field states
the value, and it is the only field added to the four records in
`UnitLifecyclePublicT1.lean` since the note of 2026-09-29. Two inherited fields,
`DecoderNewTotal` and `EncoderNewTotal`, are each equivalent to `div_ceil`
returning at divisor 32 (`decoderNew_iff` and `encoderNew_iff`,
`UnitSatisfiabilityErasure.lean`). `divCeilValue` implies both and states more
than they do, and both stay in the records, so it replaces neither.
`AeadSealBounded` replaced `AeadSealTotal` at the same count only because
`AeadSealTotal` was one of the counted contracts. So `divCeilValue` is a
fourteenth session contract. #217 did not reopen this decision. This note does,
and recuts the cap at fourteen. The tag `tacenta-assurance-v0.4.5` and main at
#220 were reached after #217 and before this note, so each has a fourteenth
contract under a cap of thirteen. No change is made to `chunk_count` in
`tacenta-core/erasure/src/lib.rs`, the one production call of `usize::div_ceil`.
Replacing that call with arithmetic that Aeneas translates would remove this
contract. It changes a verified zone and regenerates the translation, so it is a
separate change, and this note counts the contract instead. The separate witness
is `divCeilValue_shape_satisfiable`, tied to the statement of `DivCeilValue` by
`SessionBraidReceiveRepair.DivCeilValue_is` (`SessionBraidReceiveRepair.lean`);
both are pinned and on `attest.py`'s required-pin floor, so deleting either is
refused. The joint model also satisfies the law (`model_DivCeilValue` and
`UnitSatisfiabilityJoint.DivCeilValue_is`, held by `all_shapes_are_predicates` and
`model_satisfies_all_axiom_shapes`, both required pins). That is the witness in the
session unit's satisfiability module that this decision asks for, and it holds
together with the other contracts the four records contain. The coverage theorem
`all_thirteen_contracts_satisfiable` is not renamed and still names the thirteen
witnesses of the first Session proof layer; the fourteenth is not a name of that
theorem. The five laws of the inhabitation result (#220) are a different thing.
`LawPop`, `LawAsMut`, `LawBlanketU32` and `TruncateTotal` are not fields of any of
the four contract records and no lifecycle theorem takes them:
they are assumptions of that result only, recorded in
`tacenta-proofs/LIMITATIONS.md`, and outside this budget. `DivCeilValue` is the
fifth of those five laws and is counted here because it is a record field. A law
that becomes a field of a record or a hypothesis of a lifecycle theorem is a new
contract and reopens the cap.

The complete translation requires ten new primitive contracts. Existing KDF
and unit-composition contracts are inherited and named separately; the one
fixed-width RNG contract above replaces a generic new RNG assumption. More
than fourteen new session contracts requires this decision to be reopened and
the boundary to be recut before proof work continues (twelve until the note of
2026-09-29, thirteen until the note of 2026-10-01).

## Consequences and validation

- The boundary contracts establish termination and the shape of returned
  values. They do not prove the cryptographic primitives correct or secure.
- Drop and allocator behavior remain outside the formal proof; the public
  limitations record the corresponding implementation hardening and its test
  evidence.
- The Phase 0 spike record records the reachable opaque-call inventory for the
  five proof roots. Adding a reachable primitive call without adding it to one
  of the contracts is a review finding.
- Reopen this decision if Charon traverses the boundary implementation, if a
  complete call cannot be represented by these functions, or if the
  assumption cap is exceeded.

## Review

This proposal is not an assurance result. It becomes accepted only after the
recorded rule-7 review required by the session end-to-end proof plan.
