# PROJECT-CONTROLLED DRY RUN. NOT INDEPENDENT EVIDENCE. It does not close or reclassify the open item.
"""PROJECT-CONTROLLED DRY RUN. NOT INDEPENDENT EVIDENCE. It does not close or reclassify the open item.

ML-KEM-1024 cases, from session-establishment.md "ML-KEM-1024 (FIPS 203)",
session-persistence.md "Prekey store" and mlkem-braid.md "The KEM split". The
project vectors pin the key generation, the encapsulation and the decapsulation
of one honest ciphertext per key; they do not pin the rules below, which the
pages state. The NIST ACVP known-answer files that checked `tacenta_reader.mlkem`
are not in the repository (RECORD.md, section 4).
"""

import hashlib

from _casekit import flip, registry
from tacenta_reader import braid, mlkem

CASES, case = registry()
SE = "session-establishment.md ML-KEM-1024 (FIPS 203)"
SP = "session-persistence.md Prekey store"
MB = "mlkem-braid.md The KEM split"

D = bytes(range(32))
Z = bytes(range(100, 132))
M = bytes(range(200, 232))


def _pair():
    return mlkem.keygen_internal(D, Z)


@case("KEM-01 key generation: ek is 1,568 bytes and dk is 3,168, and dk is dk_pke || ek || H(ek) || z with H = SHA3-256",
      f"{SE}: Key generation; {SP}: dk = dk_pke(1,536) || ek(1,568) || h(32) || z(32)")
def _():
    ek, dk = _pair()
    assert (len(ek), len(dk)) == (1568, 3168)
    assert dk[1536:3104] == ek
    assert dk[3104:3136] == hashlib.sha3_256(ek).digest()
    assert dk[3136:] == Z
    assert mlkem.ek_modulus_check(ek[:1536]) and mlkem.dk_hash_check(dk)


@case("KEM-02 encapsulation then decapsulation: a 1,568-byte ciphertext and a 32-byte secret, the same on both sides",
      f"{SE}: Encapsulation, Decapsulation")
def _():
    ek, dk = _pair()
    secret, ciphertext = mlkem.encaps_internal(ek, M)
    assert (len(ciphertext), len(secret)) == (1568, 32)
    assert mlkem.decaps_internal(dk, ciphertext) == secret


@case("KEM-03 implicit rejection: a ciphertext with one byte changed gives a 32-byte secret that is not the real one, with no error, and it is J(z || c) with J = SHAKE256 to 32 bytes",
      f"{SE}: Implicit rejection is kept; mlkem-braid.md The KEM split: Decapsulation")
def _():
    ek, dk = _pair()
    secret, ciphertext = mlkem.encaps_internal(ek, M)
    for at in (0, 700, 1407, 1408, 1567):
        bad = flip(ciphertext, at)
        got = mlkem.decaps_internal(dk, bad)
        assert len(got) == 32 and got != secret
        assert got == hashlib.shake_256(Z + bad).digest(32)


@case("KEM-04 the encapsulation-key check refuses a coefficient at or above q = 3329 and accepts every honest key",
      f"{SE}: Validating the encapsulation key: ByteEncode12(ByteDecode12(ek[0:1536])) equals ek[0:1536]")
def _():
    ek, _ = _pair()
    assert mlkem.ek_modulus_check(ek[:1536])
    # the first coefficient 3329 = 0xD01 in 12 bits, little-endian bit order
    bad = bytes([0x01, 0x0D]) + ek[2:1536]
    assert not mlkem.ek_modulus_check(bad)
    assert not mlkem.ek_modulus_check(ek[:1535])


@case("KEM-05 the decapsulation-key check refuses a key whose stored hash is not H of the ek inside it",
      f"{SP}: dk passes the FIPS 203 section 7.3 hash check, h equal to H over the ek inside dk")
def _():
    _, dk = _pair()
    assert mlkem.dk_hash_check(dk)
    assert not mlkem.dk_hash_check(flip(dk, 3104))
    assert not mlkem.dk_hash_check(flip(dk, 1600))     # a byte of the ek inside dk
    assert not mlkem.dk_hash_check(dk[:-1])


@case("KEM-06 the Braid's header is rho || H(ek) over all of ek, and ek_vector validates against it; one changed byte of ek_vector does not",
      f"{MB}: header = rho (32) || H(ek) (32); Validation")
def _():
    ek, _ = _pair()
    header, ek_vector = mlkem.braid_split(ek)
    assert (len(header), len(ek_vector)) == (64, 1536)
    assert header[:32] == ek[1536:] and header[32:] == hashlib.sha3_256(ek).digest()
    assert hashlib.sha3_256(ek_vector + header[:32]).digest() == header[32:]
    assert braid.validate_ek_vector(header, ek_vector)
    assert not braid.validate_ek_vector(header, flip(ek_vector, 10))

