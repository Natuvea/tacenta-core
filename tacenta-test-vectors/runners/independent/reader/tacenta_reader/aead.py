"""The AEAD, from message-format.md, "Authenticated encryption".

    p          = 16 - (len(plaintext) mod 16)             -- 1 to 16
    padded     = plaintext || p bytes, each of value p
    ciphertext = AES-256-CBC-Encrypt(enc_key, iv, padded)
    tag        = HMAC-SHA256(mac_key, AD || ciphertext)   -- 32 bytes
    output     = ciphertext || tag

A receiver (1) refuses input shorter than 32 bytes; (2) checks the tag in
constant time; (3) only then decrypts, refusing an empty or non-block-multiple
ciphertext and bad PKCS#7 padding; (4) strips the padding. "Every refusal is
an authentication failure, and none is a decode failure", and all are the
same failure: one exception class, one message.

No vector pins this construction (GAPS-2.md, vector gaps).
"""

import hmac as _hmac

from . import aes
from . import constants as K
from .kdf import hmac_sha256


class AuthenticationFailure(Exception):
    """The single AEAD refusal. Deliberately carries no reason."""

    def __init__(self):
        super().__init__("authentication failure")


# Indirection so a test can observe that nothing is decrypted before the tag
# has verified ("nothing is decrypted until the tag has verified").
_cbc_decrypt = aes.cbc_decrypt


def _check_keys(enc_key: bytes, mac_key: bytes, iv: bytes) -> None:
    # Caller misuse, not a refusal of the input: the keys come from the
    # message-key expansion (ratchet.md) and always have these widths.
    if len(enc_key) != 32 or len(mac_key) != 32 or len(iv) != K.AES_BLOCK:
        raise ValueError("AEAD keys are enc_key (32), mac_key (32), iv (16)")


def encrypt(enc_key: bytes, mac_key: bytes, iv: bytes, ad: bytes, plaintext: bytes) -> bytes:
    _check_keys(enc_key, mac_key, iv)
    p = K.AES_BLOCK - (len(plaintext) % K.AES_BLOCK)
    padded = bytes(plaintext) + bytes([p]) * p
    ciphertext = aes.cbc_encrypt(enc_key, iv, padded)
    tag = hmac_sha256(mac_key, bytes(ad) + ciphertext)
    return ciphertext + tag


def decrypt(enc_key: bytes, mac_key: bytes, iv: bytes, ad: bytes, data: bytes) -> bytes:
    _check_keys(enc_key, mac_key, iv)
    data = bytes(data)
    # 1. refuses an input shorter than 32 bytes
    if len(data) < K.AEAD_TAG_LEN:
        raise AuthenticationFailure()
    # 2. last 32 bytes are the tag; constant-time comparison
    ciphertext, tag = data[:-K.AEAD_TAG_LEN], data[-K.AEAD_TAG_LEN:]
    if not _hmac.compare_digest(hmac_sha256(mac_key, bytes(ad) + ciphertext), tag):
        raise AuthenticationFailure()
    # 3. only then decrypts
    if len(ciphertext) == 0 or len(ciphertext) % K.AES_BLOCK:
        raise AuthenticationFailure()
    padded = _cbc_decrypt(enc_key, iv, ciphertext)
    p = padded[-1]
    if not 1 <= p <= K.AES_BLOCK or padded[-p:] != bytes([p]) * p:
        raise AuthenticationFailure()
    # 4. returns the result without its last p bytes
    return padded[:-p]


def seal(message_key: bytes, ad: bytes, plaintext: bytes) -> bytes:
    """Encrypt under a 32-byte message key via the message-key expansion."""
    from .ratchet import expand_message_key
    enc, mac, iv = expand_message_key(message_key)
    return encrypt(enc, mac, iv, ad, plaintext)


def open_(message_key: bytes, ad: bytes, data: bytes) -> bytes:
    from .ratchet import expand_message_key
    enc, mac, iv = expand_message_key(message_key)
    return decrypt(enc, mac, iv, ad, data)
