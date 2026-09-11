"""AEAD cases, from message-format.md "Authenticated encryption". No vector
in tacenta-test-vectors pins this construction; AE-00 is FIPS 197's own
AES-256 example, the rest are self-consistency and refusal cases."""

import hmac as _hmac

from _casekit import accepts, flip, registry, rejects
from tacenta_reader import aead, aes
from tacenta_reader import constants as K
from tacenta_reader.kdf import hmac_sha256
from tacenta_reader.wire import DecodeError

CASES, case = registry()
MF = "message-format.md Authenticated encryption"
FAIL = aead.AuthenticationFailure

ENC = bytes(range(32))
MAC = bytes(range(100, 132))
IV = bytes(range(200, 216))
AD = b"\x00\x00\x00\x03abc" + b"\x01\x01" + b"\x55" * 100


def _tagged(ciphertext, ad=AD):
    """Attach a valid tag to arbitrary ciphertext bytes, so a refusal after the
    tag check can be reached."""
    return ciphertext + hmac_sha256(MAC, ad + ciphertext)


@case("AE-00 AES-256 known answer: FIPS 197 Appendix C.3, both directions", "FIPS 197 Appendix C.3 (AES-256)")
def _():
    rk = aes.expand_key(bytes.fromhex("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"))
    pt = bytes.fromhex("00112233445566778899aabbccddeeff")
    ct = aes.encrypt_block(rk, pt)
    assert ct.hex() == "8ea2b7ca516745bfeafc49904b496089", ct.hex()
    assert aes.decrypt_block(rk, ct) == pt


@case("AE-01 round trip for every plaintext length 0..49; ciphertext is a nonzero multiple of 16; output at least 48 bytes",
      f"{MF}: ciphertext is a nonzero multiple of 16 bytes and output is at least 48 bytes")
def _():
    for n in range(50):
        pt = bytes((i * 13) & 0xFF for i in range(n))
        out = aead.encrypt(ENC, MAC, IV, AD, pt)
        ct_len = len(out) - K.AEAD_TAG_LEN
        assert ct_len == 16 * (n // 16 + 1) and len(out) >= 48
        assert accepts(aead.decrypt, ENC, MAC, IV, AD, out) == pt


@case("AE-02 PKCS#7: p = 16 - (len mod 16), a whole block gains a full block of padding",
      f"{MF}: A plaintext that is already a whole number of blocks gains a full block of padding")
def _():
    for n, p in ((0, 16), (1, 15), (15, 1), (16, 16), (17, 15), (32, 16)):
        out = aead.encrypt(ENC, MAC, IV, AD, b"\xaa" * n)
        padded = aes.cbc_decrypt(ENC, IV, out[:-32])
        assert padded == b"\xaa" * n + bytes([p]) * p


@case("AE-03 the tag is HMAC-SHA256(mac_key, AD || ciphertext), full 32 bytes, appended, no length fields",
      f"{MF}: The HMAC input is AD then ciphertext, back to back, with no length field for either")
def _():
    out = aead.encrypt(ENC, MAC, IV, AD, b"message")
    ct, tag = out[:-32], out[-32:]
    assert tag == _hmac.new(MAC, AD + ct, "sha256").digest()
    assert ct == aes.cbc_encrypt(ENC, IV, b"message" + b"\x09" * 9)


@case("AE-04 CBC structure: first block is E(P1 xor IV), second E(P2 xor C1); equal plaintext blocks give different ciphertext blocks",
      "message-format.md: AES-256-CBC (CBC per its standard definition, GAPS-2.md G2-02)")
def _():
    rk = aes.expand_key(ENC)
    p = b"\x42" * 32
    c = aes.cbc_encrypt(ENC, IV, p)
    assert c[:16] == aes.encrypt_block(rk, bytes(a ^ b for a, b in zip(p[:16], IV)))
    assert c[16:] == aes.encrypt_block(rk, bytes(a ^ b for a, b in zip(p[16:], c[:16])))
    assert c[:16] != c[16:]


@case("AE-05 step 1: input shorter than 32 bytes is refused (0, 1, 31)", f"{MF}: 1. refuses an input shorter than 32 bytes")
def _():
    for n in (0, 1, 31):
        rejects(aead.decrypt, ENC, MAC, IV, AD, b"\x00" * n, exc=FAIL)


@case("AE-06 step 2: any change to the tag, the ciphertext or AD, or the wrong mac_key, is refused",
      f"{MF}: 2. ... refuses unless HMAC-SHA256(mac_key, AD || ciphertext) equals tag")
def _():
    out = aead.encrypt(ENC, MAC, IV, AD, b"attack at dawn")
    for off in (0, 15, 16, len(out) - 33, len(out) - 32, len(out) - 1):
        rejects(aead.decrypt, ENC, MAC, IV, AD, flip(out, off), exc=FAIL)
    rejects(aead.decrypt, ENC, MAC, IV, flip(AD, 0), out, exc=FAIL)
    rejects(aead.decrypt, ENC, MAC, IV, AD + b"\x00", out, exc=FAIL)
    rejects(aead.decrypt, ENC, bytes(32), IV, AD, out, exc=FAIL)
    rejects(aead.decrypt, ENC, MAC, IV, AD, out[:-1], exc=FAIL)
    rejects(aead.decrypt, ENC, MAC, IV, AD, out + b"\x00", exc=FAIL)
    # moving the AD/ciphertext boundary changes the bytes CONCAT would give, so no split confusion
    rejects(aead.decrypt, ENC, MAC, IV, AD[:-1], bytes([AD[-1]]) + out, exc=FAIL)


@case("AE-07 step 3: an empty ciphertext with a valid tag is refused", f"{MF}: 3. ... refuses a ciphertext that is empty")
def _():
    rejects(aead.decrypt, ENC, MAC, IV, AD, _tagged(b""), exc=FAIL)


@case("AE-08 step 3: a ciphertext whose length is not a multiple of 16 (valid tag) is refused",
      f"{MF}: 3. ... or whose length is not a multiple of 16")
def _():
    for n in (1, 15, 17, 31, 33):
        rejects(aead.decrypt, ENC, MAC, IV, AD, _tagged(b"\x11" * n), exc=FAIL)


@case("AE-09 step 3: bad padding (last byte 0, 17, 0xff, or inconsistent padding bytes) with a valid tag is refused",
      f"{MF}: 3. ... refuses unless the last byte p of the result is between 1 and 16 and the last p bytes all equal p")
def _():
    blocks = [b"\x00" * 15 + b"\x00", b"\x00" * 15 + b"\x11", b"\x00" * 15 + b"\xff",
              b"\x00" * 13 + b"\x03\x02\x03", b"\x10" * 15 + b"\x11", b"\x0e" * 15 + b"\x0f",
              b"\x00" + b"\x10" * 15]
    for padded in blocks:
        rejects(aead.decrypt, ENC, MAC, IV, AD, _tagged(aes.cbc_encrypt(ENC, IV, padded)), exc=FAIL)
    # boundary acceptances: p = 16 (full block of 0x10) and p = 1
    assert accepts(aead.decrypt, ENC, MAC, IV, AD, _tagged(aes.cbc_encrypt(ENC, IV, b"\x10" * 16))) == b""
    assert accepts(aead.decrypt, ENC, MAC, IV, AD, _tagged(aes.cbc_encrypt(ENC, IV, b"\x07" * 15 + b"\x01"))) == b"\x07" * 15


@case("AE-10 every refusal is the same authentication failure: one class, one message, never a decode failure",
      f"{MF}: Every refusal is an authentication failure, and none is a decode failure ... a padding refusal cannot be told from a tag refusal")
def _():
    out = aead.encrypt(ENC, MAC, IV, AD, b"x")
    refusals = [b"", flip(out, 0), _tagged(b""), _tagged(b"\x11" * 17),
                _tagged(aes.cbc_encrypt(ENC, IV, b"\x00" * 16))]
    seen = set()
    for bad in refusals:
        try:
            aead.decrypt(ENC, MAC, IV, AD, bad)
        except DecodeError:
            raise AssertionError("an AEAD refusal was a decode failure")
        except FAIL as e:
            seen.add((type(e), str(e), e.args))
        else:
            raise AssertionError("accepted")
    assert len(seen) == 1, seen


@case("AE-11 nothing is decrypted until the tag has verified",
      f"{MF}: 3. only then decrypts; nothing is decrypted until the tag has verified")
def _():
    calls = []
    real = aead._cbc_decrypt

    def counting(*a):
        calls.append(1)
        return real(*a)

    aead._cbc_decrypt = counting
    try:
        out = aead.encrypt(ENC, MAC, IV, AD, b"x" * 40)
        for bad in (flip(out, 3), flip(out, len(out) - 1), out[:-1], b"\x00" * 64):
            rejects(aead.decrypt, ENC, MAC, IV, AD, bad, exc=FAIL)
        assert not calls, "decrypted before the tag verified"
        aead.decrypt(ENC, MAC, IV, AD, out)
        assert calls == [1]
    finally:
        aead._cbc_decrypt = real


@case("AE-12 enc_key, mac_key and iv are bytes 0-31, 32-63 and 64-79 of the 80-byte message-key expansion, in that order; the IV is not sent, so the output is exactly ciphertext || tag",
      f"{MF}: enc_key, mac_key and iv are bytes 0 to 31, 32 to 63 and 64 to 79 of the expansion's 80-byte output, in that order ... The IV is not sent")
def _():
    from tacenta_reader.kdf import hkdf_sha256
    mk = bytes(range(32))
    out80 = hkdf_sha256(bytes(32), mk, K.MK_INFO, 80)
    enc, mac, iv = out80[:32], out80[32:64], out80[64:80]
    for pt in (b"", b"x" * 15, b"y" * 16, b"z" * 33):
        sealed = aead.seal(mk, AD, pt)
        assert sealed == aead.encrypt(enc, mac, iv, AD, pt)
        assert len(sealed) == 16 * (len(pt) // 16 + 1) + K.AEAD_TAG_LEN
        assert sealed[-32:] == hmac_sha256(mac, AD + sealed[:-32])
        assert iv not in sealed[:16] and aead.decrypt(enc, mac, iv, AD, sealed) == pt
