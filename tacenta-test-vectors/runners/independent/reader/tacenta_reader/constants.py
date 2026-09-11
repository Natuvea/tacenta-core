"""Constants, each with the spec location it was read from.

Where a value is NOT stated by the specification and had to be inferred, the
comment says so and names the GAPS-2.md (or GAPS.md) entry. As of the
specification revision this reader was updated against, every value below is
stated in the tree.
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

# CONSTANTS.md "Bundle KEM prekey length"; message-format.md, Prekey bundle
MLKEM1024_EK_LEN = 1568
# message-format.md, Initial message: "1,568 bytes for ML-KEM-1024" (ciphertext)
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

# message-format.md, Key identifiers; CONSTANTS.md ABSENT_ID
ABSENT_ID = 0

# --- message-format.md, Authenticated encryption; CONSTANTS.md AEAD tag length
AEAD_TAG_LEN = 32
AES_BLOCK = 16

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
# sparse-pq-ratchet.md, Derivations: "immediately followed by its own suffix,
# with no separator" (was a hypothesis, GAPS.md G-17; now stated).
SPQR_SEPARATOR = b""

# session-establishment.md, Notation: F is 32 bytes of 0xFF for curve25519
PQXDH_F = b"\xff" * 32

# identities-and-devices.md, Application signatures; CONSTANTS.md
APP_SIGNATURE_LABEL = b"tacenta:application-signature:v1"
APP_SIGNATURE_PREFIX = APP_SIGNATURE_LABEL + b"\xff"

# mlkem-braid.md, Parameters and derivations: the two MAC suffixes, with bytes
# given on the page (the other two are BRAID_SCKA_KEY and BRAID_AUTH_UPDATE)
BRAID_EKHEADER = b":ekheader"
BRAID_CIPHERTEXT = b":ciphertext"

# session-establishment.md, The fingerprint; CONSTANTS.md
# LAST_RESORT_HANDSHAKE_LABEL: 32 ASCII bytes, no terminator
LAST_RESORT_HANDSHAKE_LABEL = b"tacenta last-resort handshake v1"

# session-establishment.md, DecodeEC: "a key whose value is at least p"
CURVE25519_P = (1 << 255) - 19

# --- Bounds, CONSTANTS.md "Bounds"
MAX_SKIP = 1000
MAX_SKIPPED_STORE = 2000
MAX_SKIPPED_AGE = 1000
EPOCHS_KEPT = 2
MAX_CODEWORDS = 65536
MAX_LAST_RESORT_SEEN = 1024

U16_MAX = (1 << 16) - 1
U32_MAX = (1 << 32) - 1
U64_MAX = (1 << 64) - 1

# ratchet.md, Skipped keys: "The count stops at u32::MAX - 1"
MAX_EVENTS = U32_MAX - 1

# CONSTANTS.md GF(2^16) reduction polynomial; mlkem-braid.md, The erasure code.
# (Inferred from a vector in the first pass, GAPS.md G-24; now stated.)
GF_POLY = 0x1100B

# --- protobuf-profile.md, Bounds; CONSTANTS.md
PB_MAX_MESSAGE_LEN = 16384
PB_MAX_FIELD_NUMBER = 15
PB_MAX_FIELDS = 32
PB_MAX_VARINT_BYTES = 5
PB_MAX_U32 = U32_MAX

# --- session-persistence.md; CONSTANTS.md "Storage formats"
STATE_VERSION = 0x01          # ratchet, spqr, braid, triple
SESSION_VERSION = 0x01
PREKEY_STORE_VERSION = 0x04
PREKEY_STORE_VERSIONS_READ = frozenset({0x01, 0x02, 0x03, 0x04})
LABELS_TACENTA = 0x00
DIRECTION_A2B = 0x00
DIRECTION_B2A = 0x01

# Braid KEM field lengths and KEM serialisation lengths (CONSTANTS.md)
BRAID_HEADER_LEN = 64
BRAID_EK_VECTOR_LEN = 1536
BRAID_CT1_LEN = 1408
BRAID_CT2_LEN = 160
BRAID_MAC_LEN = 32
BRAID_KEY_PAIR_LEN = 11872
BRAID_ENCAPS_LEN = 2592
BRAID_MAX_TAG = 11
BRAID_FAILED_TAG = 11
# mlkem-braid.md, Chunks: header with its MAC (96), ct2 with its MAC (192)
BRAID_HDR_VALUE_LEN = BRAID_HEADER_LEN + BRAID_MAC_LEN
BRAID_CT2_VALUE_LEN = BRAID_CT2_LEN + BRAID_MAC_LEN

# session-persistence.md, Erasure coder sub-formats
ERASURE_MAX_NEEDED = 65536
ERASURE_MAX_SIZE = 65536 * CHUNK_BYTES   # 2,097,152

# session-persistence.md, Prekey store; CONSTANTS.md kem_pair layout (FIPS 203)
KEM_DK_LEN = 3168
KEM_EK_LEN = 1568
KEM_PAIR_LEN = KEM_DK_LEN + KEM_EK_LEN   # 4,736
MLKEM_Q = 3329
