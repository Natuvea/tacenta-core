"""Pass 13. identities-and-devices.md, "Identity keys", and the sentences that
apply its rule at each boundary: the initiator's bundle, the responder's initial
message, the stored session, the stored prekey store, and the verifier of a
signature.

The predicate itself (check 6) was covered in pass 12 (IV-10 to IV-14). These
cases cover what this pass added:

- why an honest key passes (IK-01);
- step 3 of Verifying a signature, and Application signatures (IK-02, IK-03);
- the initiator's order of checks and what a refusal spends (IK-04 to IK-06);
- the responder's order of checks and the read-only prekey store (IK-07, IK-08);
- the stored session and the stored prekey store (IK-09 to IK-11);
- a repeated initial message (IK-12);
- the three outcomes staying distinct (IK-13).

Every key, bundle and store is built by this reader, and nothing is taken from
a vector's bytes; the signatures under keys of mixed order are fixed data
(`idkeys_signatures.py`). Where a refusal's kind is the only thing that
shows an order, the case says so.
"""

import hashlib
import random

import cases_inventory as CI
import cases_persistence as PSC
from _casekit import accepts, registry, rejects
from idkeys_signatures import SIGNATURES
from tacenta_reader import admission, identity, pqxdh, wire
from tacenta_reader import constants as K
from tacenta_reader import curve25519 as C
from tacenta_reader import persistence as P
from tacenta_reader.curve25519 import BASE, P as PRIME, Q, _add, _decode_scalar25519, _mul, x25519, x25519_public

CASES, case = registry()
ID = "identities-and-devices.md"
IKS = f"{ID} Identity keys"
VS = f"{ID} Verifying a signature"
SE = "session-establishment.md"
SP = "session-persistence.md"
R = random.Random(20260929_13)
TORSION = CI.TORSION            # the eight points of order dividing 8, TORSION[0] the identity
u_of = CI.u_of


def rnd(n):
    return bytes(R.randrange(256) for _ in range(n))


def seeded(tag, fn, *args, **kwargs):
    """Call `fn` (one of cases_persistence's builders) with that module's random
    stream replaced by a fresh one seeded by `tag`, so what it builds does not
    depend on which cases ran before. The fixed signatures in
    `idkeys_signatures.py` are filed under the bytes of messages built this way."""
    saved = PSC.R
    PSC.R = random.Random(tag)
    try:
        return fn(*args, **kwargs)
    finally:
        PSC.R = saved


def ub(u):
    return u.to_bytes(32, "little")


def mixed_keys(pub):
    """The seven u-coordinates of P + T for a non-identity low-order T, where P
    is the point of `pub`. Each is canonical, on the curve, and not in the
    prime-order subgroup."""
    pt = CI.point_of_u(int.from_bytes(pub, "little"))
    return [ub(u_of(_add(pt, t))) for t in TORSION[1:]]


HONEST_SECRET = b"\x33" * 32
HONEST = x25519_public(HONEST_SECRET)
MIXED = mixed_keys(HONEST)                    # order 8, 4 and 2 translates
BAD_KEYS = {
    "mixed-order": MIXED[0],
    "low-order-u0": bytes(32),
    "low-order-u1": ub(1),
    "p-minus-1": ub(PRIME - 1),
    "twist-u2": ub(2),
}


# ----------------------------------------------------- signing under a torsion key

class MixedSigner:
    """A signer for the key `P + T` (P the point of an honest secret, T a
    low-order point of order `order`). Its signatures are fixed test data
    (`idkeys_signatures.py`): each satisfies the verification equation for the
    message and key it is filed under, so steps 1, 2, 4, 5 and 6 of Verifying
    a signature pass and only step 3 refuses. `sign_message` looks the
    signature up and fails when there is none for that message."""

    def __init__(self, secret, torsion_index):
        k = _decode_scalar25519(secret) % Q
        self.a = k
        pt = _add(_mul(k, BASE), TORSION[torsion_index])
        self.order = next(n for n in (2, 4, 8) if C._is_identity(_mul(n, TORSION[torsion_index])))
        self.u = ub(u_of(pt))

    def sign_message(self, message):
        key = (self.u.hex(), self.order, hashlib.sha256(message).hexdigest())
        if key not in SIGNATURES:
            raise AssertionError("no fixed signature for this message under this key")
        return bytes.fromhex(SIGNATURES[key])


def verify_without_step_3(u, msg, sig):
    """Steps 1, 2, 4, 5 and 6 of Verifying a signature, with step 3 replaced by
    the weaker test the page has since replaced ("A is not of small order")."""
    if len(u) != 32 or len(sig) != 64:
        return False
    sign = sig[63] >> 7
    s = int.from_bytes(sig[32:63] + bytes([sig[63] & 0x7F]), "little")
    A = C._edwards_from_u(u, sign)
    if s >= Q or A is None or C._is_small_order(A):
        return False
    R_point = C.decompress(sig[:32])
    if R_point is None or C._is_small_order(R_point):
        return False
    h = C._sha512_int(sig[:32] + C.compress(A) + msg) % Q
    return C.compress(_add(_mul(s, BASE), C._neg(_mul(h, A)))) == sig[:32]


# ------------------------------------------------------------------ the bundle

def kem_ek():
    """A 1,568-byte encapsulation key that passes FIPS 203 section 7.2's check."""
    return seeded(1, PSC.kem_pair)[K.KEM_DK_LEN:]


IKB_SECRET = b"\x44" * 32          # the bundle's owner (Bob)
IKA_SECRET = b"\x55" * 32          # the initiator (Alice)
SPKB_SECRET = b"\x66" * 32
OPKB_SECRET = b"\x77" * 32
EK = kem_ek()


def make_bundle(one_time=True, identity_key=None, identity_sign=None, signed_prekey=None, one_time_prekey=None,
                one_time_id=None, sign_under=IKB_SECRET, sigs=None):
    """A bundle for Bob. `identity_key` replaces the published key (the
    signatures stay those of the honest identity unless `sigs` is given)."""
    spk = signed_prekey if signed_prekey is not None else x25519_public(SPKB_SECRET)
    opk = one_time_prekey if one_time_prekey is not None else x25519_public(OPKB_SECRET)
    if sigs is None:
        sigs = (C.xeddsa_sign(sign_under, wire.encode_ec(spk), rnd(64)),
                C.xeddsa_sign(sign_under, wire.encode_kem(EK), rnd(64)))
    ik = identity_key if identity_key is not None else x25519_public(IKB_SECRET)
    if one_time_id is None:
        one_time_id = 2 if one_time else K.ABSENT_ID
    return wire.PrekeyBundle(ik, spk, sigs[0], EK, sigs[1], opk if one_time else None, 1, one_time_id, 3)


def establish(bundle, **kw):
    rng, ctr = admission.Rng(), admission.Counters()
    try:
        out = admission.initiator_prefix(bundle, IKA_SECRET, rng, ctr, **kw)
        return out, None, rng, ctr
    except Exception as e:  # noqa: BLE001
        return None, e, rng, ctr


def spent(rng, ctr):
    return (ctr.signatures_verified, len(rng.draws), ctr.agreements, ctr.encapsulations)


# ============================================================= an honest key

@case("IK-01 an honest key is never refused: the clamped scalar is a multiple of 8 in [2^254, 2^255); the multiples of q in that interval are exactly 4q, 5q, 6q and 7q; q is 5 modulo 8, so they are 4, 1, 6 and 3 modulo 8 and none is a multiple of 8; so q does not divide the scalar and kB is a point of the subgroup B generates. Every X25519 public key of a random, an all-zero, an all-ones and a low-bit-heavy secret passes, is canonical, and is the u of kB",
      f"{IKS}, Why an honest key passes: Clamping clears the low three bits and sets bit 254, so k is a multiple of 8 in [2^254, 2^255). The multiples of q in that interval are 4q, 5q, 6q and 7q, and q is 5 modulo 8, so they are congruent to 4, 1, 6 and 3 modulo 8 ... So an honest party's key is never refused")
def _():
    assert Q % 8 == 5
    lo, hi = 2 ** 254, 2 ** 255
    multiples = [m for m in range(1, 9) if lo <= m * Q < hi]
    assert multiples == [4, 5, 6, 7], multiples
    assert [(m * Q) % 8 for m in multiples] == [4, 1, 6, 3]
    secrets = [rnd(32) for _ in range(20)] + [bytes(32), b"\xff" * 32, b"\x07" * 32, b"\xf8" * 32, b"\x00" * 31 + b"\x80",
                                              b"\x01" + b"\x00" * 30 + b"\x40"]
    for secret in secrets:
        k = _decode_scalar25519(secret)
        assert k % 8 == 0 and lo <= k < hi and k % Q != 0
        pub = x25519_public(secret)
        assert wire.is_canonical_curve_key(pub) and C.is_identity_key(pub)
        assert ub(u_of(_mul(k, BASE))) == pub
        for sign in (0, 1):
            assert C._in_prime_order_subgroup(CI.point_of_u(int.from_bytes(pub, "little"), sign))
    # every honest key is also contributory against any honest peer, so nothing
    # an honest party stores or presents is refused later
    for _ in range(10):
        assert x25519(rnd(32), x25519_public(rnd(32))) != bytes(32)


# ================================================ Verifying a signature, step 3

@case("IK-02 step 3 of Verifying a signature is `qA` is the identity: a signature made under a key of mixed order (A + T for T of order 2, 4 and 8) that satisfies the equation, with a canonical u, a point on the curve, s < q and an R that is not of small order, is refused, while the same input passes the earlier `A is not of small order` step; the sign carried in the signature does not change the verdict on the key; an honest signature still verifies, with either sign convention",
      f"{VS}, step 3: A is a point of the prime-order subgroup: qA is the identity. A point of small order fails this (8A is the identity), a point with x-coordinate 0 among them whatever b is, and so does a point of mixed order ... The sign b does not change the answer")
def _():
    msg = b"a message signed under a key of mixed order"
    for idx in range(1, 8):
        signer = MixedSigner(HONEST_SECRET, idx)
        sig = signer.sign_message(msg)
        assert verify_without_step_3(signer.u, msg, sig), "the fixed signature does not satisfy the equation"
        assert C.xeddsa_verify(signer.u, msg, sig) is None, f"a signature under a mixed-order key (T index {idx}) verified"
        assert not C.is_identity_key(signer.u)
        for sign in (0, 1):
            assert not C._in_prime_order_subgroup(C._edwards_from_u(signer.u, sign))
    # a signature the reader's signer makes, and one from a signer that leaves the sign bit set
    sig = C.xeddsa_sign(HONEST_SECRET, msg, rnd(64))
    assert C.xeddsa_verify(HONEST, msg, sig) is not None
    for sign in (0, 1):
        assert C._in_prime_order_subgroup(C._edwards_from_u(HONEST, sign))


@case("IK-03 an application signature is verified only under an identity key: a verifier first applies the identity-key rule and accepts no signature under a key that fails it, saying no rather than raising; the same signature verifies under the honest key; the label still keeps the two uses apart",
      f"{ID} Application signatures: A verifier rebuilds `input` from the message and verifies the signature under the published identity key. It first applies the identity-key rule to that key (Identity keys, above) and accepts no signature under a key that fails it; error-handling.md: where a boundary can only say yes or no, such as a verifier of an application signature, it says no")
def _():
    message = b"a server's challenge"
    good = identity.sign_application(HONEST_SECRET, message, rnd(64))
    assert identity.verify_application(HONEST, message, good) is True
    assert identity.verify_application(HONEST, message + b"!", good) is False
    for idx in (1, 2, 3, 4):
        signer = MixedSigner(HONEST_SECRET, idx)
        sig = signer.sign_message(identity.application_input(message))
        assert verify_without_step_3(signer.u, identity.application_input(message), sig)
        assert identity.verify_application(signer.u, message, sig) is False
    for name, key in BAD_KEYS.items():
        assert identity.verify_application(key, message, good) is False, name
        assert identity.verify_application(key, message, bytes(64)) is False, name
    # a prekey signature carries no label, so it is not an application signature
    prekey_style = C.xeddsa_sign(HONEST_SECRET, message, rnd(64))
    assert identity.verify_application(HONEST, message, prekey_style) is False


# ===================================================== the initiator's bundle

@case("IK-04 the initiator admits an honest bundle after verifying both signatures under its identity key and only then draws its random values: two signatures verified, the ephemeral key and the encapsulation's 32 bytes drawn, in that order, then the agreements computed; the identity key admitted is the bundle's",
      f"{SE}, Sending the initial message: Alice verifies every signature in the bundle and aborts if any fails ... She then generates EKA, encapsulates ... and computes; {SE}, Primitives: Encapsulation draws 32 random bytes m")
def _():
    for one_time in (True, False):
        out, err, rng, ctr = establish(make_bundle(one_time))
        assert err is None, err
        assert out.identity_key == x25519_public(IKB_SECRET)
        assert spent(rng, ctr) == (2, 2, 4 if one_time else 3, 0), spent(rng, ctr)
        assert rng.draws == [32, 32]
        assert (out.dh[3] is not None) == one_time


@case("IK-05 a bundle whose canonical identity key is not an identity key is refused as an invalid identity key before either signature is verified, a random value drawn, an agreement computed or an encapsulation made: for a mixed-order key of each torsion order, u = 0, u = 1, u = p - 1 and u = 2, including when both prekey signatures verify under the key by every other step; the refusal is neither a decode failure nor a refused bundle",
      f"{SE}, Sending the initial message: A bundle whose canonical IKB is not an identity key (identities-and-devices.md, Identity keys) is refused as an invalid identity key. She makes that check ... before she verifies either signature, draws a random value or encapsulates, so nothing is spent on the bundle and nothing changes; {IKS}, A refusal")
def _():
    msg_spk, msg_kem = wire.encode_ec(x25519_public(SPKB_SECRET)), wire.encode_kem(EK)
    for idx in (1, 2, 3, 4, 5, 6, 7):
        signer = MixedSigner(IKB_SECRET, idx)
        sigs = (signer.sign_message(msg_spk), signer.sign_message(msg_kem))
        assert verify_without_step_3(signer.u, msg_spk, sigs[0]) and verify_without_step_3(signer.u, msg_kem, sigs[1])
        out, err, rng, ctr = establish(make_bundle(identity_key=signer.u, sigs=sigs))
        assert isinstance(err, wire.InvalidIdentityKey), (idx, err)
        assert not isinstance(err, (wire.DecodeError, wire.BundleRefused))
        assert spent(rng, ctr) == (0, 0, 0, 0), spent(rng, ctr)
    for name, key in BAD_KEYS.items():
        out, err, rng, ctr = establish(make_bundle(identity_key=key))
        assert isinstance(err, wire.InvalidIdentityKey), (name, err)
        assert spent(rng, ctr) == (0, 0, 0, 0), (name, spent(rng, ctr))
        # the bytes decode: the refusal is the initiator's, not the decoder's
        accepts(wire.decode_bundle, wire.encode_bundle(make_bundle(identity_key=key)))


@case("IK-06 the identity check follows the presence, pinning and canonical checks: with an identity key that is also not what she set out to reach, or a one-time key and identifier that disagree, or a non-canonical spelling, the refusal is that check's, not the invalid identity key; pinned to the very key that fails the rule she still refuses it as an invalid identity key; the wire decoder never returns a non-canonical key, so from bytes that is a decode failure",
      f"{SE}, Sending the initial message: She makes that check after the presence, pinning and canonical checks above and before she verifies either signature; She also refuses a bundle before encapsulating when its identity key is not the one she set out to reach (when she names one), when its one-time curve prekey and that prekey's identifier disagree about whether one is present, or when its identity key, signed prekey or one-time curve prekey is not the canonical encoding; {IKS}, A refusal: Where a boundary reads a key from bytes, a key that is not canonical is still a decode failure, and the canonical rule is applied first")
def _():
    bad = BAD_KEYS["mixed-order"]
    _, err, rng, ctr = establish(make_bundle(identity_key=bad), expected_identity=x25519_public(IKB_SECRET))
    assert isinstance(err, wire.BundleRefused) and "set out to reach" in str(err), err
    _, err, rng, ctr = establish(make_bundle(identity_key=bad, one_time=True, one_time_id=K.ABSENT_ID))
    assert isinstance(err, wire.BundleRefused) and "presence" in str(err), err
    _, err, rng, ctr = establish(make_bundle(identity_key=bad, one_time=False, one_time_id=9))
    assert isinstance(err, wire.BundleRefused) and "presence" in str(err), err
    noncanon = (int.from_bytes(bad, "little") | 1 << 255).to_bytes(32, "little")
    _, err, rng, ctr = establish(make_bundle(identity_key=noncanon))
    assert isinstance(err, wire.BundleRefused) and "canonical" in str(err), err
    for name in ("mixed-order", "p-minus-1"):
        _, err, rng, ctr = establish(make_bundle(identity_key=BAD_KEYS[name]), expected_identity=BAD_KEYS[name])
        assert isinstance(err, wire.InvalidIdentityKey), (name, err)
        assert spent(rng, ctr) == (0, 0, 0, 0)
    for key in (noncanon, ub(PRIME)):
        rejects(wire.decode_bundle, wire.encode_bundle(make_bundle(identity_key=key)), exc=wire.DecodeError)


@case("IK-07 the bundle's other curve keys are not held to the identity-key rule: a signed prekey or a one-time curve prekey of mixed order, whose signature verifies, is admitted and the agreement is contributory; a low-order one is not refused as an invalid identity key but by the contributory-agreement rule, after the random values are drawn",
      f"{SE}, Sending the initial message: The other keys of the bundle are not held to it: SPKB and a one-time curve prekey need the canonical encoding and a contributory result, and no more; {IKS}, Where the rule applies: Other curve keys are outside the rule. Ephemeral keys, prekeys and ratchet keys are held to the canonical encoding and to contributory agreement")
def _():
    spk_mixed = mixed_keys(x25519_public(SPKB_SECRET))[0]
    opk_mixed = mixed_keys(x25519_public(OPKB_SECRET))[1]
    out, err, rng, ctr = establish(make_bundle(signed_prekey=spk_mixed, one_time_prekey=opk_mixed))
    assert err is None, err
    assert spent(rng, ctr) == (2, 2, 4, 0)
    for low in (bytes(32), ub(1)):
        out, err, rng, ctr = establish(make_bundle(signed_prekey=low))
        assert isinstance(err, C.NonContributory) and not isinstance(err, wire.InvalidIdentityKey), err
        assert rng.draws == [32, 32] and ctr.signatures_verified == 2
        out, err, rng, ctr = establish(make_bundle(one_time_prekey=low))
        assert isinstance(err, C.NonContributory), err
        assert ctr.agreements == 4


# ==================================================== the responder's message

RESP_IDENTITY = b"\x88" * 32


def responder_store():
    return PSC.store(identity_secret=RESP_IDENTITY, signed_prekey_id=1, one_time=[(2, rnd(32)), (3, rnd(32))],
                     kem_id=4, kem_one_time=[(5, PSC.kem_pair(), rnd(64))], next_id=10, seen=[],
                     previous_signed=(rnd(32), 7, rnd(64)), previous_kem=None)


def initial(identity_key=None, ephemeral=None, signed=1, one_time=2, kem=5, ct=None):
    ik = identity_key if identity_key is not None else x25519_public(b"\x99" * 32)
    ek = ephemeral if ephemeral is not None else x25519_public(b"\xaa" * 32)
    return wire.encode_initial(wire.InitialMessage(
        wire.encode_ec(ik), wire.encode_ec(ek), ct if ct is not None else rnd(K.MLKEM1024_CT_LEN),
        signed, one_time, kem, rnd(120)))


def receive(store_bytes, message):
    """The store is read once from its bytes and the same object is handed to
    the responder, so a responder that changed it would show."""
    store = P.prekey_store_from_bytes(store_bytes)
    ctr = admission.Counters()
    try:
        out, err = admission.responder_prefix(store, message, ctr), None
    except Exception as e:  # noqa: BLE001
        out, err = None, e
    assert P.prekey_store_to_bytes(store) == store_bytes, "the responder changed the prekey store"
    return out, err, ctr


@case("IK-08 a responder refuses an initial message whose identity is not an identity key, as an invalid identity key, once it has found the signed prekey and the KEM prekey the message names and before it looks up a one-time prekey or decapsulates: an unknown one-time identifier or a ciphertext of the wrong length behind such an identity is still refused for the identity; an unknown signed or KEM prekey identifier is refused first, as naming a prekey the store does not hold",
      f"{SE}, Receiving the initial message: Bob refuses the message as an invalid identity key when IKA is not an identity key. He makes that check once he has found the signed prekey and the KEM prekey the message names, and before he looks up a one-time prekey, decapsulates, or uses any private key on the message, so an unknown one-time identifier or a ciphertext of the wrong length behind such an IKA is still refused for the identity")
def _():
    store = P.prekey_store_to_bytes(responder_store())
    got, err, ctr = receive(store, initial())
    assert err is None and got.stopped_at == "decapsulation", err
    for name, key in BAD_KEYS.items():
        for kwargs in ({}, {"one_time": 99}, {"ct": rnd(K.MLKEM1024_CT_LEN - 1)}, {"one_time": 99, "ct": b""}):
            got, err, ctr = receive(store, initial(identity_key=key, **kwargs))
            assert isinstance(err, wire.InvalidIdentityKey), (name, kwargs, err)
            assert (ctr.agreements, ctr.private_keys_used, ctr.stored_state_changes) == (0, 0, 0)
    # without the identity defect the same faults show their own refusals
    got, err, _ = receive(store, initial(one_time=99))
    assert isinstance(err, admission.UnknownPrekey), err
    got, err, _ = receive(store, initial(ct=rnd(K.MLKEM1024_CT_LEN + 1)))
    assert isinstance(err, pqxdh.KemCiphertextRefused), err
    # the identity check comes after the two prekeys are found
    bad = BAD_KEYS["mixed-order"]
    for kwargs in ({"signed": 99}, {"kem": 99}, {"signed": 0}, {"kem": 0}):
        got, err, _ = receive(store, initial(identity_key=bad, **kwargs))
        assert isinstance(err, admission.UnknownPrekey), (kwargs, err)
    # the retired signed prekey is found for a message that still names it
    got, err, _ = receive(store, initial(signed=7))
    assert err is None, err
    got, err, _ = receive(store, initial(identity_key=bad, signed=7))
    assert isinstance(err, wire.InvalidIdentityKey), err


@case("IK-09 a refused initial message changes nothing and the prekey store is read-only until the inner message authenticates: after every refusal above, and after a message that reaches decapsulation, the store reads back to the bytes it was offered, with no one-time prekey removed and no replay identity appended; a re-spelled identity is a decode failure, not an invalid identity key; the ephemeral key is not held to the identity-key rule",
      f"{SE}, Receiving the initial message: The refusal changes nothing; The prekey store is read-only until the ratchet message inside the initial message has authenticated. Every refusal before or during that authentication leaves the whole store exactly as it was; {IKS}, A refusal: no stored state changed; Where the rule applies: Other curve keys are outside the rule")
def _():
    store_obj = responder_store()
    store = P.prekey_store_to_bytes(store_obj)
    mixed_ephemeral = mixed_keys(x25519_public(b"\xaa" * 32))[0]
    messages = [initial(identity_key=BAD_KEYS[n]) for n in BAD_KEYS] + [
        initial(), initial(one_time=0), initial(kem=4), initial(ephemeral=mixed_ephemeral),
        initial(one_time=99), initial(ct=b"short")]
    for m in messages:
        receive(store, m)             # asserts the store is as it was after each
    got, err, _ = receive(store, initial(ephemeral=mixed_ephemeral))
    assert err is None, err          # a mixed-order ephemeral is canonical and is not held to the identity rule here
    bad = BAD_KEYS["mixed-order"]
    respelled = wire.encode_initial(wire.InitialMessage(
        wire.encode_ec(bad), wire.encode_ec(x25519_public(b"\xaa" * 32)), rnd(K.MLKEM1024_CT_LEN), 1, 2, 5, b""))
    for key in (ub(int.from_bytes(bad, "little") | 1 << 255), ub(PRIME), b"\xff" * 32):
        raw = bytearray(respelled)
        raw[3:35] = key
        got, err, _ = receive(store, bytes(raw))
        assert isinstance(err, wire.DecodeError), err


# ======================================================== the stored formats

def fresh_session(initiator, **kw):
    return (PSC.session_for(PSC.ALICE0, PSC.braid_state(1, epoch=1), **kw) if initiator
            else PSC.session_for(PSC.BOB0, PSC.braid_state(5, epoch=1), initiator=False, **kw))


def ad_for(initiator_key, responder_key):
    return wire.encode_ec(initiator_key) + wire.encode_ec(responder_key)


@case("IK-10 a reader of a stored session refuses, as inconsistent, a state whose our_identity_public or peer_identity_public is a canonical key that is not an identity key (mixed order, u = 0, u = 1, u = p - 1, u = 2), for an initiator's and a responder's session, with the associated data rebuilt so no other rule refuses it; a state written by the operations is read back; the other curve keys of the session (pending_initial's ephemeral, established_ephemeral's key) are held to the canonical encoding only, so a mixed-order or low-order one is accepted",
      f"{SP}, Session, Semantic rules: our_identity_public and peer_identity_public are each an identity key (identities-and-devices.md, Identity keys), which is stricter than canonical; Stored curve public keys: the two identity keys by its identity-key half, so a canonical identity key that is not an identity key is refused here too; {IKS}, Where the rule applies: Other curve keys are outside the rule")
def _():
    for name, key in BAD_KEYS.items():
        for initiator in (True, False):
            ours, theirs = (PSC.IKA, PSC.IKB) if initiator else (PSC.IKB, PSC.IKA)
            for field in ("our_identity_public", "peer_identity_public"):
                own, peer = (key, theirs) if field == "our_identity_public" else (ours, key)
                init_key, resp_key = (own, peer) if initiator else (peer, own)
                s = fresh_session(initiator, our_identity_public=own, peer_identity_public=peer,
                                  identity_ad=ad_for(init_key, resp_key))
                e = rejects(P.session_from_bytes, P.session_to_bytes(s), exc=P.PersistError)
                assert isinstance(e, P.Inconsistent), (name, initiator, field, type(e).__name__, e)
                assert "identity key" in str(e), e
    accepts(P.session_from_bytes, P.session_to_bytes(fresh_session(True)))
    accepts(P.session_from_bytes, P.session_to_bytes(fresh_session(False)))
    for key in list(BAD_KEYS.values()):
        accepts(P.session_from_bytes, P.session_to_bytes(fresh_session(True, pending_initial=P.PendingInitial(key, rnd(1568), 1, 2, 3))))
        accepts(P.session_from_bytes, P.session_to_bytes(fresh_session(False, established_ephemeral=wire.encode_ec(key))))


@case("IK-11 a reader of a stored prekey store refuses, as malformed and before any signature is checked, a store whose identity_public is a canonical key that is not an identity key, in each of the five versions: with signatures that verify under the key by every step but the prime-order one, with signatures that do not verify, and with the honest identity's; the refusal is not incoherent; a store with an honest identity and one bad signature is still incoherent",
      f"{SP}, Prekey store, Semantic rules: identity_public is an identity key ... A store that fails this rule is refused as malformed, before any signature is checked; Rejection: the prekey store calls it incoherent and gives it for its signature rule alone, its other rules being malformed")
def _():
    honest = PSC.store(identity_secret=IKB_SECRET)
    for version in (1, 2, 3, 4, 5):
        def raw(p):
            return P.prekey_store_to_bytes(p) if version == 5 else PSC.legacy(p, version)

        accepts(P.prekey_store_from_bytes, raw(honest))
        for name, key in BAD_KEYS.items():
            # signatures that do not verify under the replaced key
            e = rejects(P.prekey_store_from_bytes, raw(PSC.store(identity_public=key, unsigned=True)), exc=P.PersistError)
            assert type(e) is P.Malformed and "identity key" in str(e), (version, name, type(e).__name__, e)
            # the honest identity's signatures, kept under the replaced key
            e = rejects(P.prekey_store_from_bytes, raw(PSC.store(identity_public=key)), exc=P.PersistError)
            assert type(e) is P.Malformed, (version, name, type(e).__name__, e)
        # every signature verifies under a mixed-order identity by the earlier step 3: still malformed
        signer = MixedSigner(IKB_SECRET, 3)
        p = seeded(100 + version, PSC.store, identity_public=signer.u, unsigned=True)
        p.signed_prekey_sig = signer.sign_message(wire.encode_ec(x25519_public(p.signed_prekey_secret)))
        p.kem_sig = signer.sign_message(wire.encode_kem(p.kem_pair[K.KEM_DK_LEN:]))
        p.kem_one_time = [(i, kp, signer.sign_message(wire.encode_kem(kp[K.KEM_DK_LEN:]))) for i, kp, _ in p.kem_one_time]
        assert verify_without_step_3(signer.u, wire.encode_ec(x25519_public(p.signed_prekey_secret)), p.signed_prekey_sig)
        e = rejects(P.prekey_store_from_bytes, raw(p), exc=P.PersistError)
        assert type(e) is P.Malformed, (version, type(e).__name__, e)
        broken = PSC.store(identity_secret=IKB_SECRET)
        broken.signed_prekey_sig = bytes([broken.signed_prekey_sig[0] ^ 1]) + broken.signed_prekey_sig[1:]
        e = rejects(P.prekey_store_from_bytes, raw(broken), exc=P.PersistError)
        assert type(e) is P.Incoherent, (version, type(e).__name__, e)


@case("IK-12 a caller that means to adopt a reader with the rule can find the states it will refuse beforehand by reading the identity keys of every stored state and applying the rule to each: the scan names the keys of a stored session and of a stored prekey store that fail the rule, names none for an honest state, and reads a state the reader would refuse for another reason",
      f"{SP}, Session, Semantic rules: A session or store written before the identity-key rule existed may be refused by a reader that has it ... A caller that means to adopt a reader with the rule can find the states it will refuse beforehand by reading the identity keys of every stored state and applying the rule to each; tacenta-core provides this as scan_stored_session_identities and scan_stored_prekey_identity")
def _():
    honest = P.session_to_bytes(fresh_session(True))
    assert P.scan_stored_session_identities(honest) == []
    bad = BAD_KEYS["mixed-order"]
    s = P.session_to_bytes(fresh_session(True, peer_identity_public=bad, identity_ad=ad_for(PSC.IKA, bad)))
    assert P.scan_stored_session_identities(s) == [("peer_identity_public", bad)]
    both = P.session_to_bytes(fresh_session(False, our_identity_public=BAD_KEYS["low-order-u0"], peer_identity_public=bad,
                                            identity_ad=ad_for(bad, BAD_KEYS["low-order-u0"])))
    assert [n for n, _ in P.scan_stored_session_identities(both)] == ["our_identity_public", "peer_identity_public"]
    # a state the reader refuses for another reason (a ratchet_private that is not the private half of dhs_pub) is still scanned
    other = P.session_to_bytes(fresh_session(True, ratchet_private=rnd(32), peer_identity_public=bad, identity_ad=ad_for(PSC.IKA, bad)))
    rejects(P.session_from_bytes, other, exc=P.PersistError)
    assert P.scan_stored_session_identities(other) == [("peer_identity_public", bad)]
    store = PSC.store(identity_secret=IKB_SECRET)
    assert P.scan_stored_prekey_identity(P.prekey_store_to_bytes(store)) == []
    old = PSC.legacy(PSC.store(identity_public=bad, unsigned=True), 3)
    assert P.scan_stored_prekey_identity(old) == [("identity_public", bad)]
    # neither scan changes or deletes anything: the bytes are as they were
    assert P.scan_stored_session_identities(s) == P.scan_stored_session_identities(s)


# ============================================================ a repeat

@case("IK-13 a repeated initial message is matched on the identity by bytes, which is enough because the session holds only an identity key and an identity key has one canonical spelling: a genuine repeat is accepted; a repeat naming any of the other seven torsion spellings of the peer's identity, or any non-identity key, is refused as not a repeat and changes nothing; of the eight spellings X25519 reads alike, exactly one is an identity key",
      f"{SE}, Receiving the initial message: The repeat check therefore uses the agreement class for ephemeral and byte equality for identity. Byte equality is enough for identity, because the session holds only an identity key, and an identity key has one canonical spelling (identities-and-devices.md, Identity keys)")
def _():
    s = P.session_from_bytes(P.session_to_bytes(PSC.BOB_S))
    peer = s.peer_identity_public
    assert C.is_identity_key(peer)
    spellings = [ub(u_of(_add(CI.point_of_u(int.from_bytes(peer, "little")), t))) for t in TORSION]
    assert len(set(spellings)) == 8 and spellings.count(peer) == 1
    assert [C.is_identity_key(k) for k in spellings].count(True) == 1
    for k in spellings:
        assert x25519(b"\x5a" * 32, k) == x25519(b"\x5a" * 32, peer)

    def repeat(identity_key):
        raw = wire.encode_initial(wire.InitialMessage(wire.encode_ec(identity_key), s.established_ephemeral,
                                                      rnd(K.MLKEM1024_CT_LEN), 1, 2, 3, b"inner"))
        return pqxdh.receive_repeated_initial(s, raw, lambda inner: b"opened")

    assert accepts(repeat, peer) == b"opened"
    for k in spellings:
        if k != peer:
            rejects(repeat, k, exc=pqxdh.NotARepeatedInitial)
    for key in BAD_KEYS.values():
        rejects(repeat, key, exc=pqxdh.NotARepeatedInitial)
    assert P.session_to_bytes(s) == P.session_to_bytes(PSC.BOB_S)


@case("IK-14 an invalid identity key is a third outcome beside decode failure and authentication failure: the three are different refusals in this reader, a non-canonical spelling read from bytes stays a decode failure with the canonical rule applied first, a signature that does not verify is an authentication failure, and a canonical key that fails the rule is an invalid identity key; a verifier that can only say yes or no says no",
      "error-handling.md, What is required: An invalid identity key is a third outcome ... An implementation reports it as its own refusal wherever it can, and where a boundary can only say yes or no, such as a verifier of an application signature, it says no. A key that is not canonical is still a decode failure; " + IKS + ", A refusal")
def _():
    assert not issubclass(wire.InvalidIdentityKey, wire.DecodeError)
    assert not issubclass(wire.DecodeError, wire.InvalidIdentityKey)
    assert not issubclass(wire.InvalidIdentityKey, wire.BundleRefused)
    noncanon = ub(int.from_bytes(BAD_KEYS["mixed-order"], "little") | 1 << 255)
    rejects(identity.admit_identity_key, noncanon, exc=wire.DecodeError)
    rejects(identity.admit_identity_key, BAD_KEYS["mixed-order"], exc=wire.InvalidIdentityKey)
    rejects(identity.admit_identity_key, BAD_KEYS["p-minus-1"], exc=wire.InvalidIdentityKey)
    assert identity.admit_identity_key(HONEST) == HONEST
    # not read from bytes: a non-canonical key handed to the rule alone fails the rule
    rejects(identity.admit_identity_key, noncanon, read_from_bytes=False, exc=wire.InvalidIdentityKey)
    # an authentication failure is a signature that does not verify under an identity key
    sig = C.xeddsa_sign(HONEST_SECRET, b"m", rnd(64))
    assert C.xeddsa_verify(HONEST, b"n", sig) is None and C.is_identity_key(HONEST)


@case("IK-15 the wire's decoders do not test which keys are identity keys: a prekey bundle's identity_key and an initial message's identity, and a ratchet message's dh, decode in every canonical spelling, a key of mixed order, u = 0, u = 1, u = p - 1 and u = 2 included, and are held to the identity-key rule afterwards by the party that admits them; the non-canonical spellings are still decode failures",
      "message-format.md, Curve public keys: The rule is on what the wire's decoders accept. A decoder reads bytes and does not test which keys are identity keys: a bundle's identity_key and an initial message's identity are held to the identity-key rule after they decode, by the party that admits them (identities-and-devices.md, Identity keys)")
def _():
    for name, key in BAD_KEYS.items():
        b = accepts(wire.decode_bundle, wire.encode_bundle(make_bundle(identity_key=key)))
        assert b.identity_key == key
        m = accepts(wire.decode_initial, initial(identity_key=key))
        assert m.identity == wire.encode_ec(key)
        header = wire.CompositeHeader(dh=key, pn=0, n=0, pq_epoch=1, pq_n=0, ag_epoch=1, ag_type=K.AG_NONE, codeword=None)
        accepts(wire.decode_composite, wire.encode_composite(header))
        # then held to the rule by the party that admits them
        assert not C.is_identity_key(key)
    for key in (ub(int.from_bytes(BAD_KEYS["mixed-order"], "little") | 1 << 255), ub(PRIME), ub(PRIME + 1)):
        rejects(wire.decode_bundle, wire.encode_bundle(make_bundle(identity_key=key)), exc=wire.DecodeError)
        rejects(wire.decode_initial, initial(identity_key=key), exc=wire.DecodeError)


@case("IK-16 a state the reader refuses is not repaired, changed or deleted by the reader: the refused session's and prekey store's bytes, offered as a mutable buffer, are as they were after the refusal, and no key is dropped or substituted (no state is returned)",
      f"{SP}, Session, Semantic rules: The reader refuses such a state (a session as inconsistent, a store as malformed) and does not repair it, drop the key or substitute another. The refused bytes are not deleted by the reader, and its secrets are where they were")
def _():
    bad = BAD_KEYS["mixed-order"]
    session = bytearray(P.session_to_bytes(fresh_session(True, peer_identity_public=bad, identity_ad=ad_for(PSC.IKA, bad))))
    store = bytearray(P.prekey_store_to_bytes(PSC.store(identity_public=bad, unsigned=True)))
    for reader, buf in ((P.session_from_bytes, session), (P.prekey_store_from_bytes, store)):
        before = bytes(buf)
        try:
            out = reader(buf)
        except P.PersistError:
            out = None
        assert out is None and bytes(buf) == before


@case("IK-17 the hosted inventory statement's issuer key is a key the signature is verified under, read as the u of Verifying a signature whatever it is: an issuer key of mixed order under which a statement's signature satisfies the equation is a signature that does not verify (an authentication failure), not an unbound issuer; the same statement signed by an honest issuer is accepted",
      f"{ID} Accepting a signed statement, check 3: The 32 bytes the binding returns are read as the key `u` of Verifying a signature, whatever they are, and the message `M` is the input above, so a key that fails steps 1 to 6 there is a signature that does not verify, not an unbound issuer; {VS}, step 3")
def _():
    from tacenta_reader import inventory as INV
    statement = INV.Statement(7, b"acme/alice", 5, (), 1, ())
    unsigned = INV.encode_unsigned(statement)
    honest_signed = unsigned + C.xeddsa_sign(IKB_SECRET, INV.signing_input(unsigned), rnd(64))
    asked = b"acme/alice"
    accepts(INV.accept, honest_signed, asked, CI.Rec(key=x25519_public(IKB_SECRET), account=asked, kid=7))
    for idx in (1, 2, 4):
        signer = MixedSigner(IKB_SECRET, idx)
        sig = signer.sign_message(INV.signing_input(unsigned))
        assert verify_without_step_3(signer.u, INV.signing_input(unsigned), sig)
        e = rejects(INV.accept, unsigned + sig, asked, CI.Rec(key=signer.u, account=asked, kid=7), exc=INV.InventoryRefusal)
        assert isinstance(e, INV.AuthenticationFailure) and e.check == "signature", (idx, type(e).__name__, e)
    for name, key in BAD_KEYS.items():
        e = rejects(INV.accept, honest_signed, asked, CI.Rec(key=key, account=asked, kid=7), exc=INV.InventoryRefusal)
        assert isinstance(e, INV.AuthenticationFailure), (name, type(e).__name__)
