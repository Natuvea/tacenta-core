"""Hosted device-inventory statements (pass 12).

From identities-and-devices.md, "Hosted device-inventory statements" and its
subsection "Accepting a signed statement", with the constants of CONSTANTS.md
("Derivation labels" and "Bounds"), message-format.md "Curve public keys" for
the canonical rule, and the same page's "Signing" and "Verifying a signature"
for the issuer signature. Nothing here is taken from a vector's bytes.

The page's structure, as modelled:

- the unsigned preimage and the `DeviceBinding` and `Revocation` encodings,
  with every encoding rule the page states ("is refused"), applied the same way
  to bytes and to a statement built in memory ("A statement that breaks an
  encoding rule is refused before check 1, whether it arrived as bytes or was
  built in memory");
- `binding_commitment`;
- the signed statement: the preimage followed by a 64-byte XEdDSA signature
  over `"Tacenta:inventory-statement:v1" || 0xFF || unsigned_preimage`;
- the seven ordered checks a verifier applies, with the verifier's own parts
  (issuer-key binding, freshness rule, binding policy and statement policy)
  supplied by the caller as a policy object;
- the issuer's duty to apply the encoding rules, check 5 and check 6 before it
  signs.

Refusal kinds (the page's second paragraph): a refusal by an encoding rule is
a decode failure, a refusal by check 3 is an authentication failure
(error-handling.md), and the other checks refuse a statement that is well formed
and authentic. Each refusal carries the name of the check that made it, in the
words tacenta-test-vectors/README.md uses for `refusal`.
"""

import hashlib
from dataclasses import dataclass
from typing import Optional, Sequence

from .curve25519 import P, Q, _inv, _is_identity, _mul, _recover_x, xeddsa_sign, xeddsa_verify

# CONSTANTS.md, Derivation labels. The domain has no terminator (the page:
# "the ASCII string `Tacenta Inventory Statement v1`"); the two labels end in
# 0xFF (the page writes `"..." || 0xFF`; CONSTANTS.md writes `\xff`).
INVENTORY_DOMAIN = b"Tacenta Inventory Statement v1"
INVENTORY_SIGNING_LABEL = b"Tacenta:inventory-statement:v1" + b"\xff"
BINDING_COMMITMENT_LABEL = b"Tacenta:inventory-binding-commitment:v1" + b"\xff"

# CONSTANTS.md, Bounds.
GROUP_EPOCH_V1 = 1
MAX_ACCOUNT_BYTES = 256
MAX_ACTIVE_BINDINGS = 8
MAX_RECENT_REVOCATIONS = 8

SIGNATURE_LEN = 64
U32_MAX = 2 ** 32 - 1
U64_MAX = 2 ** 64 - 1

# The nine names tacenta-test-vectors/README.md gives `refusal`, in check order.
CHECKS = ("decode", "account", "issuer", "signature", "freshness",
          "duplicate-device", "identity-key", "binding-policy", "statement-policy")


# ----------------------------------------------------------------- refusals

class InventoryRefusal(Exception):
    """A refusal; `check` names the check that made it."""
    check = None

    def __init__(self, check, reason=""):
        super().__init__(f"{check}: {reason}" if reason else check)
        self.check = check


class DecodeFailure(InventoryRefusal):
    """An encoding rule: "A refusal by an encoding rule is a decode failure"."""

    def __init__(self, reason):
        super().__init__("decode", reason)


class AuthenticationFailure(InventoryRefusal):
    """Check 3: "a refusal by check 3 below is an authentication failure"."""

    def __init__(self, reason="the signature does not verify under the resolved key"):
        super().__init__("signature", reason)


class StatementRefused(InventoryRefusal):
    """Checks 1, 2 and 4 to 7: "The other checks refuse a statement that is
    well formed and authentic"."""


class IssuerRefusal(Exception):
    """The issuer's duty: it "must not sign one that fails any of them"."""


# ------------------------------------------------------------------- values

@dataclass(frozen=True)
class DeviceBinding:
    device_id: int
    identity_public_key: bytes
    capabilities: int
    replacement_predecessor: Optional[bytes] = None   # present exactly when the tag is 1


@dataclass(frozen=True)
class Revocation:
    """"`Revocation` appends `terminal_generation` (u64) to a `DeviceBinding`"."""
    binding: DeviceBinding
    terminal_generation: int


@dataclass(frozen=True)
class Statement:
    issuer_key_id: int
    account_handle: bytes
    inventory_generation: int
    active: tuple
    revocation_floor_generation: int
    revoked: tuple


def _u(value, bits, what):
    if not isinstance(value, int) or isinstance(value, bool) or not 0 <= value < 2 ** bits:
        raise DecodeFailure(f"{what} is not a u{bits}")
    return value.to_bytes(bits // 8, "big")


# ----------------------------------------------------------------- encoding

def encode_binding(binding: DeviceBinding) -> bytes:
    """`DeviceBinding`: device_id u32, identity_public_key 32 bytes,
    capabilities u64, replacement_predecessor_tag u8 (0 or 1), and the 32-byte
    predecessor only when the tag is 1. "Version one defines only capability
    bit `GROUP_EPOCH_V1` (`1`): the capability word is non-zero and no other
    bit is set." A binding that breaks it "has no encoding"."""
    if not isinstance(binding, DeviceBinding):
        raise DecodeFailure("not a DeviceBinding")
    key = binding.identity_public_key
    if not isinstance(key, (bytes, bytearray)) or len(key) != 32:
        raise DecodeFailure("identity_public_key is not 32 bytes")
    caps = _u(binding.capabilities, 64, "capabilities")
    if binding.capabilities == 0 or binding.capabilities & ~GROUP_EPOCH_V1:
        raise DecodeFailure("capability word is not exactly GROUP_EPOCH_V1")
    out = _u(binding.device_id, 32, "device_id") + bytes(key) + caps
    pred = binding.replacement_predecessor
    if pred is None:
        return out + b"\x00"
    if not isinstance(pred, (bytes, bytearray)) or len(pred) != 32:
        raise DecodeFailure("replacement_predecessor is not 32 bytes")
    return out + b"\x01" + bytes(pred)


def encode_revocation(revocation: Revocation) -> bytes:
    if not isinstance(revocation, Revocation):
        raise DecodeFailure("not a Revocation")
    return encode_binding(revocation.binding) + _u(revocation.terminal_generation, 64, "terminal_generation")


def _strictly_ascending(encodings: Sequence[bytes]) -> bool:
    """"Both lists are sorted in strictly ascending order of their encodings,
    compared as unsigned byte strings from the first byte, so each entry's
    encoding is greater than the one before it and no entry repeats." Python's
    bytes comparison is that comparison."""
    return all(a < b for a, b in zip(encodings, encodings[1:]))


def check_encoding_rules(s: Statement) -> None:
    """Every rule the section states above "The unsigned decoder refuses an
    input that breaks any rule above"; raises DecodeFailure."""
    if not isinstance(s, Statement):
        raise DecodeFailure("not a Statement")
    _u(s.issuer_key_id, 64, "issuer_key_id")
    _u(s.inventory_generation, 64, "inventory_generation")
    _u(s.revocation_floor_generation, 64, "revocation_floor_generation")
    account = s.account_handle
    if not isinstance(account, (bytes, bytearray)):
        raise DecodeFailure("account_handle is not bytes")
    # "The account handle is non-empty and at most MAX_ACCOUNT_BYTES (256)
    # bytes; invalid UTF-8 is refused."
    if len(account) == 0:
        raise DecodeFailure("account handle is empty")
    if len(account) > MAX_ACCOUNT_BYTES:
        raise DecodeFailure("account handle is longer than MAX_ACCOUNT_BYTES")
    try:
        bytes(account).decode("utf-8", errors="strict")
    except UnicodeDecodeError as e:
        raise DecodeFailure(f"account handle is not valid UTF-8: {e.reason}") from None
    active, revoked = tuple(s.active), tuple(s.revoked)
    # "`active_count` is at most MAX_ACTIVE_BINDINGS (8), and `revoked_count`
    # is at most MAX_RECENT_REVOCATIONS (8)."
    if len(active) > MAX_ACTIVE_BINDINGS:
        raise DecodeFailure("active_count is above MAX_ACTIVE_BINDINGS")
    if len(revoked) > MAX_RECENT_REVOCATIONS:
        raise DecodeFailure("revoked_count is above MAX_RECENT_REVOCATIONS")
    # "The floor is no greater than `inventory_generation`."
    if s.revocation_floor_generation > s.inventory_generation:
        raise DecodeFailure("revocation_floor_generation is above inventory_generation")
    active_enc = [encode_binding(b) for b in active]
    revoked_enc = [encode_revocation(r) for r in revoked]
    # "`active` orders the `DeviceBinding` encodings and `revoked` orders the
    # `Revocation` encodings."
    if not _strictly_ascending(active_enc):
        raise DecodeFailure("active is not in strictly ascending encoded order")
    if not _strictly_ascending(revoked_enc):
        raise DecodeFailure("revoked is not in strictly ascending encoded order")
    for r in revoked:
        # "Each terminal generation is greater than `revocation_floor_generation`
        # and no greater than `inventory_generation`"
        if not s.revocation_floor_generation < r.terminal_generation <= s.inventory_generation:
            raise DecodeFailure("terminal_generation is outside (floor, inventory_generation]")
    # "an exact binding cannot occur in both `active` and `revoked`": the same
    # exact binding is "when their encodings are equal"; the terminal
    # generation "belongs to a `Revocation`, not to its binding".
    active_set = set(active_enc)
    for r in revoked:
        if encode_binding(r.binding) in active_set:
            raise DecodeFailure("an exact binding occurs in both active and revoked")


def encode_unsigned(s: Statement) -> bytes:
    """The unsigned preimage, all integers big-endian."""
    check_encoding_rules(s)
    return (INVENTORY_DOMAIN
            + _u(s.issuer_key_id, 64, "issuer_key_id")
            + _u(len(s.account_handle), 32, "account_handle_length") + bytes(s.account_handle)
            + _u(s.inventory_generation, 64, "inventory_generation")
            + _u(len(s.active), 32, "active_count") + b"".join(encode_binding(b) for b in s.active)
            + _u(s.revocation_floor_generation, 64, "revocation_floor_generation")
            + _u(len(s.revoked), 32, "revoked_count") + b"".join(encode_revocation(r) for r in s.revoked))


# ----------------------------------------------------------------- decoding

class _Cursor:
    def __init__(self, data: bytes):
        self.data, self.off = bytes(data), 0

    def take(self, n, what):
        if n > len(self.data) - self.off:
            raise DecodeFailure(f"input ends inside {what}")
        out = self.data[self.off:self.off + n]
        self.off += n
        return out

    def uint(self, n, what):
        return int.from_bytes(self.take(n, what), "big")


def _read_binding(c: _Cursor) -> DeviceBinding:
    device_id = c.uint(4, "device_id")
    key = c.take(32, "identity_public_key")
    caps = c.uint(8, "capabilities")
    tag = c.uint(1, "replacement_predecessor_tag")
    # "replacement_predecessor_tag  u8, 0 or 1; any other value is refused"
    if tag == 0:
        pred = None
    elif tag == 1:
        pred = c.take(32, "replacement_predecessor")
    else:
        raise DecodeFailure(f"replacement_predecessor_tag is {tag}, not 0 or 1")
    if caps == 0 or caps & ~GROUP_EPOCH_V1:
        raise DecodeFailure("capability word is not exactly GROUP_EPOCH_V1")
    return DeviceBinding(device_id, key, caps, pred)


def decode_unsigned(data: bytes) -> Statement:
    """"The unsigned decoder refuses an input that breaks any rule above. It
    must consume exactly the bytes above, so trailing bytes are refused, and it
    must refuse a value whose re-encoding differs from the input.\""""
    c = _Cursor(data)
    if c.take(len(INVENTORY_DOMAIN), "INVENTORY_DOMAIN") != INVENTORY_DOMAIN:
        raise DecodeFailure("the input does not begin with INVENTORY_DOMAIN")
    issuer_key_id = c.uint(8, "issuer_key_id")
    account_len = c.uint(4, "account_handle_length")
    if account_len == 0:
        raise DecodeFailure("account handle is empty")
    if account_len > MAX_ACCOUNT_BYTES:
        raise DecodeFailure("account handle is longer than MAX_ACCOUNT_BYTES")
    account = c.take(account_len, "account_handle")
    generation = c.uint(8, "inventory_generation")
    active_count = c.uint(4, "active_count")
    if active_count > MAX_ACTIVE_BINDINGS:
        raise DecodeFailure("active_count is above MAX_ACTIVE_BINDINGS")
    active = tuple(_read_binding(c) for _ in range(active_count))
    floor = c.uint(8, "revocation_floor_generation")
    revoked_count = c.uint(4, "revoked_count")
    if revoked_count > MAX_RECENT_REVOCATIONS:
        raise DecodeFailure("revoked_count is above MAX_RECENT_REVOCATIONS")
    revoked = []
    for _ in range(revoked_count):
        b = _read_binding(c)
        revoked.append(Revocation(b, c.uint(8, "terminal_generation")))
    if c.off != len(c.data):
        raise DecodeFailure(f"{len(c.data) - c.off} trailing bytes")
    s = Statement(issuer_key_id, account, generation, active, floor, tuple(revoked))
    check_encoding_rules(s)
    if encode_unsigned(s) != bytes(data):
        raise DecodeFailure("the re-encoding differs from the input")
    return s


def signing_input(unsigned: bytes) -> bytes:
    """`"Tacenta:inventory-statement:v1" || 0xFF || unsigned_preimage`."""
    return INVENTORY_SIGNING_LABEL + bytes(unsigned)


def decode_signed(data: bytes):
    """"A signed statement is the unsigned preimage followed by a 64-byte
    XEdDSA signature". The preimage is self-delimiting, so the last 64 bytes
    are the signature and the rest must decode exactly (GAPS-12.md G12-03 on
    what the page says of a signed input's length). Returns (statement,
    unsigned bytes, signature)."""
    data = bytes(data)
    if len(data) < SIGNATURE_LEN:
        raise DecodeFailure("shorter than a signature")
    unsigned, signature = data[:-SIGNATURE_LEN], data[-SIGNATURE_LEN:]
    return decode_unsigned(unsigned), unsigned, signature


def binding_commitment(binding: DeviceBinding) -> bytes:
    """SHA-256 of `"Tacenta:inventory-binding-commitment:v1" || 0xFF ||
    encode(binding)`. "A binding whose capability word breaks the rule above
    has no encoding, so it has no commitment and the function refuses it.\""""
    return hashlib.sha256(BINDING_COMMITMENT_LABEL + encode_binding(binding)).digest()


# ------------------------------------------------------------------ check 6

def is_identity_key(u_bytes: bytes) -> bool:
    """Check 6: "a canonical curve public key (message-format.md, Curve public
    keys) whose u-coordinate belongs to a point of the prime-order subgroup of
    edwards25519 ... A verifier tests that in three steps. `u` is not p - 1.
    `y = (u - 1) / (u + 1) mod p` is the y-coordinate of a point `P` of
    edwards25519 (Verifying a signature, step 2). And `qP` is the identity; the
    two points with that y-coordinate give the same answer, so the sign of x
    does not matter.\""""
    if not isinstance(u_bytes, (bytes, bytearray)) or len(u_bytes) != 32:
        return False
    u = int.from_bytes(u_bytes, "little")
    if u >= P:                      # canonical: the 256-bit value is below p
        return False
    if u == P - 1:                  # step one
        return False
    y = (u - 1) * _inv(u + 1) % P   # step two
    x = _recover_x(y, 0)
    if x is None:
        return False
    point = (x, y, 1, x * y % P)
    return _is_identity(_mul(Q, point))   # step three


# ---------------------------------------------------------------- the checks

class Policy:
    """The verifier's own parts. The page names four: the caller-supplied
    issuer-key binding (check 2), the freshness rule (check 4), and the
    binding and statement policies (check 7). `accepted` is where a verifier
    records a generation: "only after check 7 has accepted the statement".
    What happens to a statement whose compare-and-advance then fails is not
    stated (GAPS-12.md G12-04); here the statement stays accepted."""

    def issuer_key(self, issuer_key_id: int, account_handle: bytes) -> Optional[bytes]:
        raise NotImplementedError

    def fresh(self, account_handle: bytes, generation: int) -> bool:
        raise NotImplementedError

    def accept_binding(self, binding: DeviceBinding, status: str) -> bool:
        raise NotImplementedError

    def accept_statement(self, statement: Statement) -> bool:
        raise NotImplementedError

    def accepted(self, statement: Statement) -> None:
        pass


def duplicate_active_device(s: Statement) -> bool:
    """Check 5: "No two entries of `active` share a `device_id`." An active and
    a revoked binding may share one."""
    ids = [b.device_id for b in s.active]
    return len(ids) != len(set(ids))


def unsound_key(s: Statement) -> Optional[DeviceBinding]:
    """Check 6 over "every entry, those of `active` and then those of `revoked`,
    each in encoded order"; the first binding whose key is refused, or None."""
    for b in list(s.active) + [r.binding for r in s.revoked]:
        if not is_identity_key(b.identity_public_key):
            return b
    return None


def _checks(s: Statement, unsigned: bytes, signature: bytes, asked_account: bytes, policy: Policy) -> Statement:
    # 1. "`account_handle` equals, byte for byte, the account the verifier
    #    asked about. This comes before any lookup"
    if bytes(s.account_handle) != bytes(asked_account):
        raise StatementRefused("account", "the statement is for another account")
    # 2. "The verifier's issuer-key binding resolves `(issuer_key_id,
    #    account_handle)` to a verification key. An unbound issuer is refused."
    key = policy.issuer_key(s.issuer_key_id, bytes(s.account_handle))
    if key is None:
        raise StatementRefused("issuer", "the issuer is unbound")
    # 3. "The signature verifies under that key." Verification is the page's
    #    own, "Verifying a signature" (GAPS-12.md G12-02).
    if xeddsa_verify(bytes(key), signing_input(unsigned), bytes(signature)) is None:
        raise AuthenticationFailure()
    # 4. "The verifier's freshness rule accepts `inventory_generation` for the
    #    account." It "must have no effect of its own".
    if not policy.fresh(bytes(s.account_handle), s.inventory_generation):
        raise StatementRefused("freshness", "the freshness rule refuses the generation")
    # 5.
    if duplicate_active_device(s):
        raise StatementRefused("duplicate-device", "two active entries share a device_id")
    # 6. every entry, before check 7 is applied to any binding
    bad = unsound_key(s)
    if bad is not None:
        raise StatementRefused("identity-key", f"{bad.identity_public_key.hex()} is not an identity key")
    # 7. "It then applies the binding policy to the entries of `active` in
    #    encoded order and then to the entries of `revoked` in encoded order,
    #    telling it the binding and which list it came from, and stops at the
    #    first refusal. The statement policy runs only when every binding has
    #    been accepted, and it is given the whole statement as verified."
    for b in s.active:
        if not policy.accept_binding(b, "active"):
            raise StatementRefused("binding-policy", "the binding policy refuses an active entry")
    for r in s.revoked:
        if not policy.accept_binding(r.binding, "revoked"):
            raise StatementRefused("binding-policy", "the binding policy refuses a revoked entry")
    if not policy.accept_statement(s):
        raise StatementRefused("statement-policy", "the statement policy refuses the statement")
    policy.accepted(s)
    return s


def accept(signed: bytes, asked_account: bytes, policy: Policy) -> Statement:
    """A signed statement as bytes. "A statement that breaks an encoding rule
    is refused before check 1"; then the seven checks in order, refusing on the
    first that fails. Returns the statement as verified."""
    s, unsigned, signature = decode_signed(signed)
    return _checks(s, unsigned, signature, asked_account, policy)


def accept_built(s: Statement, signature: bytes, asked_account: bytes, policy: Policy) -> Statement:
    """A statement "built in memory", with its signature: the encoding rules
    apply to it just as to bytes, before check 1."""
    unsigned = encode_unsigned(s)
    if not isinstance(signature, (bytes, bytearray)) or len(signature) != SIGNATURE_LEN:
        raise DecodeFailure("the signature is not 64 bytes")
    return _checks(s, unsigned, bytes(signature), asked_account, policy)


def sign_statement(issuer_secret: bytes, s: Statement, z: bytes) -> bytes:
    """"An issuer must apply the encoding rules, check 5 and check 6 below to a
    statement before it signs it, and must not sign one that fails any of
    them". Returns the signed statement: preimage || signature."""
    try:
        unsigned = encode_unsigned(s)
    except DecodeFailure as e:
        raise IssuerRefusal(f"encoding rule: {e}") from None
    if duplicate_active_device(s):
        raise IssuerRefusal("check 5: two active entries share a device_id")
    if unsound_key(s) is not None:
        raise IssuerRefusal("check 6: an identity_public_key is not an identity key")
    return unsigned + xeddsa_sign(issuer_secret, signing_input(unsigned), z)
