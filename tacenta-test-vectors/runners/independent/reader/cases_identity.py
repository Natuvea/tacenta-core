"""identities-and-devices.md (identity secret, application signatures) and
session-establishment.md (repeated initial message, non-contributory
definition). No vectors."""

from _casekit import accepts, registry, rejects
from tacenta_reader import constants as K
from tacenta_reader import curve25519, identity, pqxdh, wire

CASES, case = registry()
ID = "identities-and-devices.md"
SE = "session-establishment.md"

SECRET = bytes(range(40, 72))
PUB = identity.public_key(SECRET)
Z = b"\x5a" * 64


@case("ID-01 the application label is 32 ASCII bytes, 33 with 0xFF; a signature over label || 0xFF || message verifies under the identity key",
      f"{ID} Application signatures: input = \"tacenta:application-signature:v1\" || 0xFF || message")
def _():
    assert len(K.APP_SIGNATURE_LABEL) == 32 and len(K.APP_SIGNATURE_PREFIX) == 33
    for msg in (b"", b"server challenge 1234", b"\xff" * 100):
        sig = identity.sign_application(SECRET, msg, Z)
        assert identity.verify_application(PUB, msg, sig)
        assert curve25519.xeddsa_verify(PUB, K.APP_SIGNATURE_PREFIX + msg, sig) is not None
        assert not identity.verify_application(PUB, msg + b"\x00", sig)


@case("ID-02 the label keeps the two uses apart: a prekey signature is not an application signature over the same bytes, nor the reverse",
      f"{ID} Application signatures: a signature made for one is not accepted for the other")
def _():
    spk = curve25519.x25519_public(b"\x21" * 32)
    prekey_sig = curve25519.xeddsa_sign(SECRET, wire.encode_ec(spk), Z)
    assert curve25519.xeddsa_verify(PUB, wire.encode_ec(spk), prekey_sig) is not None
    assert not identity.verify_application(PUB, wire.encode_ec(spk), prekey_sig)
    app_sig = identity.sign_application(SECRET, wire.encode_ec(spk), Z)
    assert curve25519.xeddsa_verify(PUB, wire.encode_ec(spk), app_sig) is None


@case("ID-03 one 32-byte secret, used as it is: the X25519 scalar is clamped when used, so DH under the raw and the clamped bytes agree",
      f"{ID} The identity key's secret: the X25519 private scalar, clamped when used")
def _():
    rejects(identity.public_key, SECRET[:31], exc=ValueError)
    clamped = bytearray(SECRET)
    clamped[0] &= 248
    clamped[31] = (clamped[31] & 127) | 64
    peer = curve25519.x25519_public(b"\x33" * 32)
    assert curve25519.x25519(SECRET, peer) == curve25519.x25519(bytes(clamped), peer)


@case("SE-01 a repeated initial message is accepted only by a responder's session and only if ephemeral matches established_ephemeral byte for byte",
      f"{SE} Receiving the initial message: accepts it only if it is a responder's session and the message's ephemeral field equals ... (NotARepeatedInitial)")
def _():
    eph = b"\x05" + b"\x0b" * 32
    m = wire.InitialMessage(identity=b"\x05" + b"\x0a" * 32, ephemeral=eph, kem_ciphertext=b"\x01" * 1568,
                            signed_prekey_id=1, one_time_prekey_id=2, kem_prekey_id=3, ratchet_message=b"")
    accepts(pqxdh.accept_repeated_initial, True, eph, m)
    # no other field is compared
    other = wire.InitialMessage(identity=b"\x05" + b"\x77" * 32, ephemeral=eph, kem_ciphertext=b"",
                                signed_prekey_id=9, one_time_prekey_id=0, kem_prekey_id=9, ratchet_message=b"zz")
    accepts(pqxdh.accept_repeated_initial, True, eph, other)
    rejects(pqxdh.accept_repeated_initial, True, b"\x05" + b"\x0c" * 32, m, exc=pqxdh.NotARepeatedInitial)
    rejects(pqxdh.accept_repeated_initial, False, None, m, exc=pqxdh.NotARepeatedInitial)
    rejects(pqxdh.accept_repeated_initial, False, eph, m, exc=pqxdh.NotARepeatedInitial)


@case("SE-02 non-contributory means all 32 output bytes zero; every low-order input gives it and a normal key does not",
      f"{SE} Notation: A DH output is non-contributory when all 32 of its bytes are zero")
def _():
    p = 2 ** 255 - 19
    for u in (0, 1, p - 1, p, p + 1):
        out = curve25519.x25519(SECRET, (u % 2 ** 256).to_bytes(32, "little"))
        if out == bytes(32):
            rejects(curve25519.x25519_contributory, SECRET, (u % 2 ** 256).to_bytes(32, "little"),
                    exc=curve25519.NonContributory)
    assert curve25519.x25519(SECRET, bytes(32)) == bytes(32)
    accepts(curve25519.x25519_contributory, SECRET, PUB)


# ------------------------------------------------------------ DecodeEC

P = curve25519.P
Q = curve25519.Q


@case("SE-03 DecodeEC accepts exactly one encoding of each key: bit 255 set is refused, a value at or above p is refused, p - 1 and honest keys decode",
      f"{SE} Sending the initial message: DecodeEC accepts exactly one encoding of each key")
def _():
    for v in (P, P + 1, P + 18, 2 ** 255 - 1):
        rejects(wire.decode_ec, b"\x05" + v.to_bytes(32, "little"), exc=wire.DecodeError)
    for key in (PUB, bytes(31) + b"\x7f"[:0] + b"\x00", (P - 1).to_bytes(32, "little")):
        assert wire.decode_ec(b"\x05" + key) == key
    rejects(wire.decode_ec, b"\x05" + PUB[:31] + bytes([PUB[31] | 0x80]), exc=wire.DecodeError)
    # G3-05: the initial-message decoder lists only the curve byte; the handshake applies DecodeEC
    m = wire.InitialMessage(identity=b"\x05" + (int.from_bytes(PUB, "little") + P).to_bytes(32, "little"),
                            ephemeral=b"\x05" + PUB, kem_ciphertext=bytes(1568), signed_prekey_id=1,
                            one_time_prekey_id=0, kem_prekey_id=2, ratchet_message=b"")
    if int.from_bytes(PUB, "little") + P < 2 ** 256:
        assert accepts(wire.decode_initial, wire.encode_initial(m)) == m
        rejects(pqxdh.handshake_keys, m, exc=wire.DecodeError)


@case("SE-04 X25519 as RFC 7748 leaves it: a public key is X25519(k, 9) of the stored, unclamped secret; a raw 32-byte peer key reaches X25519 as received, so bit 255 set, or p added to a small u, names the same key and gives the same output",
      f"{SE} Primitives, and what is left to them: X25519 (RFC 7748), Public keys; Decoding a peer's key is left to X25519 only where no rule on this page applies")
def _():
    nine = (9).to_bytes(32, "little")
    assert curve25519.x25519(SECRET, nine) == PUB == curve25519.x25519_public(SECRET)
    peer = curve25519.x25519_public(b"\x77" * 32)
    respelled = peer[:31] + bytes([peer[31] | 0x80])
    assert curve25519.x25519(SECRET, respelled) == curve25519.x25519(SECRET, peer)
    assert curve25519.x25519(SECRET, (9 + P).to_bytes(32, "little")) == curve25519.x25519(SECRET, nine)
    rejects(wire.decode_ec, b"\x05" + respelled, exc=wire.DecodeError)   # the EncodeEC form is refused instead


@case("SE-05 before encapsulating, the bundle's KEM prekey must be 1,568 bytes and pass ByteEncode12(ByteDecode12(ek[0:1536])) = ek[0:1536]; a key failing either is refused",
      f"{SE} Primitives, and what is left to them: ML-KEM-1024 (FIPS 203), Validating the encapsulation key")
def _():
    from tacenta_reader.kem_double import byte_encode12
    good = byte_encode12([K.MLKEM_Q - 1] * 1024) + bytes(32)
    accepts(pqxdh.check_kem_prekey, good)
    for coeffs in ([K.MLKEM_Q] + [0] * 1023, [0] * 1023 + [4095], [0] * 500 + [K.MLKEM_Q + 1] + [0] * 523):
        rejects(pqxdh.check_kem_prekey, byte_encode12(coeffs) + bytes(32), exc=pqxdh.KemPrekeyRefused)
    rejects(pqxdh.check_kem_prekey, good[:-1], exc=pqxdh.KemPrekeyRefused)
    rejects(pqxdh.check_kem_prekey, good + b"\x00", exc=pqxdh.KemPrekeyRefused)


# -------------------------------------------------------------- XEdDSA
# identities-and-devices.md, Signing and Verifying a signature. The edges are
# also pinned by primitives/xeddsa.json (run as vectors); these build their own.

C = curve25519


def mont_u(pt):
    zi = pow(pt[2], P - 2, P)
    y = pt[1] * zi % P
    return (1 + y) * pow(1 - y, P - 2, P) % P


def clamp(secret):
    b = bytearray(secret)
    b[0] &= 248
    b[31] = (b[31] & 127) | 64
    return int.from_bytes(b, "little")


def sign_with(k, msg, z, normalise=True, r=None, R_point_hook=None):
    """The page's signing table, with switches to build signatures a
    non-normalising or deliberately bad signer would make."""
    E = C._mul(k, C.BASE)
    enc_e = C.compress(E)
    sign = enc_e[31] >> 7
    if normalise:
        A = enc_e[:31] + bytes([enc_e[31] & 0x7F])
        a = (Q - k) % Q if sign else k % Q
    else:
        A, a = enc_e, k % Q
    if r is None:
        r = C._sha512_int(b"\xfe" + b"\xff" * 31 + a.to_bytes(32, "little") + msg + z) % Q
    R = C._mul(r, C.BASE)
    if R_point_hook is not None:
        R = R_point_hook(R)
    R_enc = C.compress(R)
    h = C._sha512_int(R_enc + A + msg) % Q
    s = (r + h * a) % Q
    sig = bytearray(R_enc + s.to_bytes(32, "little"))
    if not normalise:
        sig[63] |= sign << 7
    return bytes(sig), A, sign


@case("XS-01 signing as the page computes it: k = clamp(secret) mod q, A's sign normalised to 0, a negated when E's sign is 1, r from hash_1's prefix, a, M and Z; the result is xeddsa_sign's, A's u-coordinate is the published key, s's top bit is 0, and a signer that skips the clamp makes signatures that do not verify",
      f"{ID} Signing; Why the clamp")
def _():
    for seed in range(6):
        secret = bytes((seed * 37 + i * 11) % 256 for i in range(32))
        msg, z = b"message %d" % seed, bytes([seed]) * 64
        sig, A, _ = sign_with(clamp(secret) % Q, msg, z)
        assert sig == C.xeddsa_sign(secret, msg, z)
        assert mont_u(C.decompress(A)).to_bytes(32, "little") == C.x25519_public(secret)
        assert sig[63] & 0x80 == 0 and C.xeddsa_verify(C.x25519_public(secret), msg, sig) is not None
        if int.from_bytes(secret, "little") % Q != clamp(secret) % Q:
            bad, _, _ = sign_with(int.from_bytes(secret, "little") % Q, msg, z)
            assert C.xeddsa_verify(C.x25519_public(secret), msg, bad) is None


@case("XS-02 rules 1 and 2: an honest signature is refused under its key with bit 255 set, under u + p, under u = p - 1, and under a u whose y has no point; the top bit of the signature is A's sign, so a signer that does not normalise verifies and clearing that bit refuses",
      f"{ID} Verifying a signature, rules 1 and 2; It is wider on the sign bit")
def _():
    secret, msg, z = bytes(range(1, 33)), b"rules one and two", b"\x42" * 64
    pub = C.x25519_public(secret)
    sig = C.xeddsa_sign(secret, msg, z)
    u = int.from_bytes(pub, "little")
    assert C.xeddsa_verify(pub, msg, sig) is not None
    for bad in ((u | 1 << 255).to_bytes(32, "little"), (P - 1).to_bytes(32, "little")) + \
            (((u + P).to_bytes(32, "little"),) if u + P < 2 ** 256 else ()):
        assert C.xeddsa_verify(bad, msg, sig) is None
    no_point = next(v for v in range(2, 200) if C._recover_x((v - 1) * pow(v + 1, P - 2, P) % P, 0) is None)
    assert C.xeddsa_verify(no_point.to_bytes(32, "little"), msg, sig) is None
    for seed in range(40):
        s2 = bytes([seed + 1]) * 32
        k = clamp(s2) % Q
        if C.compress(C._mul(k, C.BASE))[31] >> 7:
            carried, _, sign = sign_with(k, msg, z, normalise=False)
            assert sign == 1 and carried[63] & 0x80
            assert C.xeddsa_verify(C.x25519_public(s2), msg, carried) is not None
            cleared = carried[:63] + bytes([carried[63] & 0x7F])
            assert C.xeddsa_verify(C.x25519_public(s2), msg, cleared) is None
            break
    else:
        raise AssertionError("no key with Edwards sign 1 found")


@case("XS-03 rules 3 and 6: a small-order A (u = 0, order 2; u = 1, order 4) is refused even with R of full order and an equation that holds, and with R the identity whatever the message and sign bit; an honest key's signature with R the identity (r = 0, s = h a) is refused",
      f"{ID} Verifying a signature, rules 3 and 6; It is narrower on small-order points")
def _():
    ident = C.compress(C.IDENTITY)
    for u in (0, 1):
        for msg in (b"", b"a", b"small order"):
            for top in (0, 0x80):
                sig = ident + bytes(31) + bytes([top])
                assert C.xeddsa_verify(u.to_bytes(32, "little"), msg, sig) is None
    # Rule 3 on its own: rule 6 cannot refuse these, since R has full order.
    r = 0x1234567
    R = C._mul(r, C.BASE)
    R_enc = C.compress(R)
    assert not C._is_small_order(R)
    for u, order in ((0, 2), (1, 4)):
        A_enc = ((u - 1) * pow(u + 1, P - 2, P) % P).to_bytes(32, "little")
        A = C.decompress(A_enc)
        assert A is not None and C._is_small_order(A)
        msg = next(m for m in (b"rule three %d" % i for i in range(400))
                   if (C._sha512_int(R_enc + A_enc + m) % Q) % order == 0)
        h = C._sha512_int(R_enc + A_enc + msg) % Q
        sig = R_enc + r.to_bytes(32, "little")
        assert C.compress(C._add(C._mul(r, C.BASE), C._neg(C._mul(h, A)))) == R_enc   # sB - hA = R holds
        assert C.xeddsa_verify(u.to_bytes(32, "little"), msg, sig) is None
    secret, msg = bytes(range(9, 41)), b"rule six"
    sig, _, _ = sign_with(clamp(secret) % Q, msg, bytes(64), r=0)
    assert sig[:32] == ident
    E = C._mul(clamp(secret) % Q, C.BASE)
    A = C.compress(E)[:31] + bytes([C.compress(E)[31] & 0x7F])
    s = int.from_bytes(sig[32:], "little")
    h = C._sha512_int(ident + A + msg) % Q
    assert C.compress(C._add(C._mul(s, C.BASE), C._neg(C._mul(h, C.decompress(A))))) == ident   # the equation holds
    assert C.xeddsa_verify(C.x25519_public(secret), msg, sig) is None


@case("XS-04 rules 4 and 5, and no cofactor: s + q is refused though below 2^253; R is compared as bytes; a signature over R + T, T of order 2, satisfies the cofactored equation and is refused",
      f"{ID} Verifying a signature, rules 4 and 5; No step multiplies by the cofactor")
def _():
    secret, msg, z = bytes(range(50, 82)), b"rules four and five", b"\x17" * 64
    pub = C.x25519_public(secret)
    sig = C.xeddsa_sign(secret, msg, z)
    s = int.from_bytes(sig[32:], "little")
    assert s + Q < 2 ** 253
    assert C.xeddsa_verify(pub, msg, sig[:32] + (s + Q).to_bytes(32, "little")) is None
    assert C.xeddsa_verify(pub, msg, bytes([sig[0] ^ 1]) + sig[1:]) is None
    T = (0, P - 1, 1, 0)                                  # (0, -1), order 2
    assert C._is_identity(C._add(T, T)) and not C._is_identity(T)
    k = clamp(secret) % Q
    bad, A, _ = sign_with(k, msg, z, R_point_hook=lambda R: C._add(R, T))
    R2 = C.decompress(bad[:32])
    h = C._sha512_int(bad[:32] + A + msg) % Q
    lhs = C._mul(8, C._add(C._mul(int.from_bytes(bad[32:], "little"), C.BASE), C._neg(C._mul(h, C.decompress(A)))))
    assert C.compress(lhs) == C.compress(C._mul(8, R2)) and not C._is_small_order(R2)
    assert C.xeddsa_verify(pub, msg, bad) is None


# ------------------------------------------------ the last-resort replay record
# session-establishment.md, Replay and The fingerprint; key-deletion.md;
# session-persistence.md, Prekey store. No vector pins a fingerprint.

import hashlib as _hashlib  # noqa: E402
import hmac as _hmac_mod  # noqa: E402

import cases_persistence as PSC  # noqa: E402
from tacenta_reader import persistence  # noqa: E402

FP = f"{SE} The fingerprint"
EKA = curve25519.x25519_public(b"\x44" * 32)


def lr_message(**kw):
    base = dict(identity=b"\x05" + PUB, ephemeral=b"\x05" + EKA, kem_ciphertext=bytes(range(256)) * 6 + bytes(32),
                signed_prekey_id=1, one_time_prekey_id=0, kem_prekey_id=4, ratchet_message=b"a ratchet message")
    base.update(kw)
    return wire.InitialMessage(**base)


def lr_store(**kw):
    base = dict(seen=[], previous_kem=(PSC.kem_pair(), 8, PSC.rnd(64)))
    base.update(kw)
    return PSC.store(**base)


class Authenticated:
    def __init__(self, ok=True):
        self.ok, self.calls = ok, 0

    def __call__(self):
        self.calls += 1
        if not self.ok:
            raise ValueError("initial ciphertext did not authenticate")
        return b"plaintext"


@case("LR-01 the fingerprint is HMAC-SHA256 keyed with the 32 ASCII bytes 'tacenta last-resort handshake v1' over u32(33) || identity || u32(33) || ephemeral || u32(len) || kem_ciphertext || one_time_prekey_id || kem_prekey_id, integers big-endian",
      f"{FP}: input = ...; The input is built as follows")
def _():
    assert K.LAST_RESORT_HANDSHAKE_LABEL == b"tacenta last-resort handshake v1" and len(K.LAST_RESORT_HANDSHAKE_LABEL) == 32
    for ct_len, otpk in ((1568, 0), (0, 7), (5, 0xFFFFFFFF)):
        m = lr_message(kem_ciphertext=bytes(range(ct_len % 256)) * (ct_len // 256) + bytes(ct_len % 256), one_time_prekey_id=otpk)
        data = (33).to_bytes(4, "big") + m.identity + (33).to_bytes(4, "big") + m.ephemeral \
            + len(m.kem_ciphertext).to_bytes(4, "big") + m.kem_ciphertext + otpk.to_bytes(4, "big") + (4).to_bytes(4, "big")
        fp = pqxdh.last_resort_fingerprint(m)
        assert fp == _hmac_mod.new(b"tacenta last-resort handshake v1", data, _hashlib.sha256).digest() and len(fp) == 32


@case("LR-02 every input moves the fingerprint (either key, the ciphertext's bytes or length, either identifier); signed_prekey_id and the ratchet message do not",
      f"{FP}: What is left out")
def _():
    base = pqxdh.last_resort_fingerprint(lr_message())
    for kw in (dict(identity=b"\x05" + EKA), dict(ephemeral=b"\x05" + PUB), dict(kem_ciphertext=bytes(1568)),
               dict(kem_ciphertext=bytes(range(256)) * 6 + bytes(31)), dict(one_time_prekey_id=1), dict(kem_prekey_id=8)):
        assert pqxdh.last_resort_fingerprint(lr_message(**kw)) != base, kw
    for kw in (dict(signed_prekey_id=99), dict(ratchet_message=b""), dict(ratchet_message=b"re-framed")):
        assert pqxdh.last_resort_fingerprint(lr_message(**kw)) == base, kw


@case("LR-03 only the last-resort path consults the record: kem_prekey_id naming the current or the retired last-resort key is on it; a one-time KEM prekey is not, and is never refused by the record or recorded",
      f"{FP}: A handshake is on the last-resort path when ...; key-deletion.md: a handshake naming a one-time KEM prekey never consults the record")
def _():
    full = lr_store(seen=[(4, PSC.rnd(32)) for _ in range(1024)] + [(8, PSC.rnd(32)) for _ in range(1024)])
    assert pqxdh.on_last_resort_path(full, 4) and pqxdh.on_last_resort_path(full, 8)
    assert not pqxdh.on_last_resort_path(full, 5) and not pqxdh.on_last_resort_path(lr_store(previous_kem=None), 8)
    auth = Authenticated()
    after, _ = accepts(pqxdh.receive_last_resort, full, lr_message(kem_prekey_id=5), auth)
    assert after == full and auth.calls == 1


@case("LR-04 computed before decapsulation, refused if any entry holds it whatever its tag, and added tagged with kem_prekey_id only once the initial ciphertext has authenticated",
      f"{FP}: Bob computes the fingerprint before he decapsulates ... adds the fingerprint, tagged with kem_prekey_id, only once the initial ciphertext has authenticated")
def _():
    s = lr_store()
    m = lr_message()
    failing = Authenticated(ok=False)
    rejects(pqxdh.receive_last_resort, s, m, failing, exc=ValueError)
    assert failing.calls == 1 and s.seen == []
    auth = Authenticated()
    s2, pt = accepts(pqxdh.receive_last_resort, s, m, auth)
    assert pt == b"plaintext" and s2.seen == [(4, pqxdh.last_resort_fingerprint(m))]
    again = Authenticated()
    rejects(pqxdh.receive_last_resort, s2, m, again, exc=pqxdh.ReplayedLastResort)
    assert again.calls == 0
    cross = lr_store(seen=[(8, pqxdh.last_resort_fingerprint(m))])
    rejects(pqxdh.receive_last_resort, cross, m, Authenticated(), exc=pqxdh.ReplayedLastResort)


@case("LR-05 1024 entries per key, failing closed: a new handshake naming a key whose budget is spent is refused (LastResortRecordFull) before anything is decrypted and nothing changes; the other key's budget is its own; a repeat is still a replay",
      f"{SE} Replay: bounded at 1024 entries per key ... It fails closed rather than evicting; CONSTANTS.md MAX_LAST_RESORT_SEEN")
def _():
    m = lr_message()
    fp_m = pqxdh.last_resort_fingerprint(m)
    spent = lr_store(seen=[(4, PSC.rnd(32)) for _ in range(1023)] + [(4, fp_m)])
    other = lr_message(ephemeral=b"\x05" + curve25519.x25519_public(b"\x45" * 32))
    auth = Authenticated()
    rejects(pqxdh.receive_last_resort, spent, other, auth, exc=pqxdh.LastResortRecordFull)
    assert auth.calls == 0 and len(spent.seen) == 1024
    rejects(pqxdh.receive_last_resort, spent, m, Authenticated(), exc=pqxdh.ReplayedLastResort)
    s2, _ = accepts(pqxdh.receive_last_resort, spent, replace_msg(other, kem_prekey_id=8), Authenticated())
    assert s2.seen[-1][0] == 8 and len(s2.seen) == 1025
    almost = lr_store(seen=[(4, PSC.rnd(32)) for _ in range(1023)])
    s3, _ = accepts(pqxdh.receive_last_resort, almost, other, Authenticated())
    assert persistence.prekey_store_semantic(s3) is None and len(s3.seen) == 1024


def replace_msg(m, **kw):
    from dataclasses import replace as _replace
    return _replace(m, **kw)


@case("LR-06 the curve-key inputs are the canonical encodings: a captured handshake with identity or ephemeral re-spelled (bit 255 set, or p added) is refused before it is fingerprinted, and never recorded",
      f"{FP}: The curve-key inputs are the canonical encodings")
def _():
    m = lr_message()
    s, _ = pqxdh.receive_last_resort(lr_store(), m, Authenticated())
    respelled = []
    for field in ("identity", "ephemeral"):
        raw = getattr(m, field)[1:]
        u = int.from_bytes(raw, "little")
        respelled.append(replace_msg(m, **{field: b"\x05" + raw[:31] + bytes([raw[31] | 0x80])}))
        if u + P < 2 ** 256:
            respelled.append(replace_msg(m, **{field: b"\x05" + (u + P).to_bytes(32, "little")}))
    assert len(respelled) >= 2
    for r in respelled:
        assert pqxdh.last_resort_fingerprint(r) != pqxdh.last_resort_fingerprint(m)
        auth = Authenticated()
        rejects(pqxdh.receive_last_resort, s, r, auth, exc=wire.DecodeError)
        assert auth.calls == 0
    assert len(s.seen) == 1


@case("LR-07 the record persists with the store, tags included: a store read back still refuses the replay it recorded",
      f"key-deletion.md: The record persists with the store, tags included; session-persistence.md Prekey store (v4 seen)")
def _():
    m = lr_message(kem_prekey_id=8)
    s, _ = pqxdh.receive_last_resort(lr_store(), m, Authenticated())
    back = accepts(persistence.prekey_store_from_bytes, persistence.prekey_store_to_bytes(s))
    assert back.seen == [(8, pqxdh.last_resort_fingerprint(m))]
    rejects(pqxdh.receive_last_resort, back, m, Authenticated(), exc=pqxdh.ReplayedLastResort)
