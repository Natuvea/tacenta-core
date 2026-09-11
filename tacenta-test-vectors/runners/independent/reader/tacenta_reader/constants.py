"""Constants, each with the spec location it was read from.

Where a value was NOT stated by the spec and had to be inferred from a vector
or from a hypothesis, the comment says so and names the GAPS.md entry.
"""

# --- message-format.md, "Wire-sensitive values"; CONSTANTS.md "Wire encodings"
VERSION = 0x01
TYPE_RATCHET = 0x01
TYPE_INITIAL = 0x02
TYPE_BUNDLE = 0x03

# session-establishment.md, Parameters; CONSTANTS.md
ENCODE_EC_BYTE = 0x05
ENCODE_KEM_BYTE = 0x08
EC_KEY_LEN = 32
ENCODED_EC_LEN = 33

# message-format.md, Prekey bundle ("1,568 bytes for ML-KEM-1024")
MLKEM1024_EK_LEN = 1568
# CONSTANTS.md, Storage formats, "Braid KEM field lengths" (ct1 + ct2 = 1,568)
MLKEM1024_CT_LEN = 1568
BUNDLE_LEN_MLKEM1024 = 1811

SIGNATURE_LEN = 64

# message-format.md, Ratchet message: "The composite header is 102 bytes"
COMPOSITE_LEN = 102
# CONSTANTS.md CHUNK_BYTES
CHUNK_BYTES = 32

# message-format.md, ag_type table; CONSTANTS.md AgreementType bytes
AG_NONE = 0x00
AG_HDR = 0x01
AG_EK = 0x02
AG_EK_CT1_ACK = 0x03
AG_CT1 = 0x04
AG_CT2 = 0x05
AG_TYPES = frozenset({AG_NONE, AG_HDR, AG_EK, AG_EK_CT1_ACK, AG_CT1, AG_CT2})

# message-format.md, presence byte; CONSTANTS.md
PRESENT = 0x01
ABSENT = 0x00

# message-format.md, Key identifiers
ABSENT_ID = 0

# --- Derivation labels, CONSTANTS.md "Derivation labels"
RK_INFO = b"Tacenta RK"
MK_INFO = b"Tacenta MK"
SK_INFO = b"Tacenta_CURVE25519_SHA-256_ML-KEM-1024"
COMBINE_INFO = b"Tacenta_CURVE25519_SHA-256_MLKEM1024"
SPLIT_INFO = COMBINE_INFO + b":Split"
BRAID_PROTOCOL_INFO = b"Tacenta_MLKEM1024_SHA-256"
BRAID_SCKA_KEY = b":SCKA Key"
BRAID_AUTH_UPDATE = b":Authenticator Update"
SPQR_PROTOCOL_INFO = b"Tacenta SPQR"
SPQR_CHAIN_START = b"Chain Start"
SPQR_ROOT = b"Root"
SPQR_CHAIN = b"Chain"
# How PROTOCOL_INFO and the suffix are joined ("followed by") is not stated;
# plain concatenation with no separator is a hypothesis confirmed by
# spqr.json (GAPS.md G-17).
SPQR_SEPARATOR = b""

# session-establishment.md, Notation: F is 32 bytes of 0xFF for curve25519
PQXDH_F = b"\xff" * 32

# --- Bounds, CONSTANTS.md "Bounds"
MAX_SKIP = 1000
MAX_SKIPPED_STORE = 2000
MAX_SKIPPED_AGE = 1000
EPOCHS_KEPT = 2
MAX_CODEWORDS = 65536

U32_MAX = (1 << 32) - 1
U64_MAX = (1 << 64) - 1

# GF(2^16) reduction polynomial. NOT stated anywhere in the spec; inferred
# from gf.json vector "doubling-folds" (0x8000 * 2 = 0x100b), GAPS.md G-24.
GF_POLY = 0x1100B
