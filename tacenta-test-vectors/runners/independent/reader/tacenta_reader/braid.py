"""ML-KEM Braid derivations named by protocol/mlkem-braid.md and CONSTANTS.md.

mlkem-braid.md defers to the published ML-KEM Braid specification for the
protocol and restates none of the derivations; the spec tree carries only the
suffix literals and PROTOCOL_INFO. The constructions below are hypotheses
(GAPS.md G-22, G-23; still open in GAPS-2.md), confirmed by braid.json and
auth.json. The Braid state machine, the header/ciphertext MACs and the KEM
are not implemented; the erasure code is (erasure.py), and the Braid's
persisted layout is (persistence.py).
"""

from typing import Tuple

from . import constants as K
from .kdf import hkdf_sha256


def _epoch(epoch: int) -> bytes:
    # mlkem-braid.md: "Epochs are unsigned 64-bit integers, big-endian on the wire."
    if epoch < 0 or epoch > K.U64_MAX:
        raise ValueError("epoch out of range")
    return epoch.to_bytes(8, "big")


def kdf_epoch_key(ss: bytes, epoch: int) -> bytes:
    """Epoch key from the KEM shared secret and the epoch alone."""
    return hkdf_sha256(bytes(32), ss, K.BRAID_PROTOCOL_INFO + K.BRAID_SCKA_KEY + _epoch(epoch), 32)


def auth_update(root_key: bytes, key: bytes, epoch: int) -> Tuple[bytes, bytes]:
    """Ratcheted Authenticator update -> (new root key, MAC key)."""
    out = hkdf_sha256(root_key, key, K.BRAID_PROTOCOL_INFO + K.BRAID_AUTH_UPDATE + _epoch(epoch), 64)
    return out[:32], out[32:]
