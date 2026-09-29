"""The four `vectors/groups/inventory-*.json` layouts (pass 12).

tacenta-test-vectors/README.md, Vector layouts, "The hosted-inventory
statements". Each file has a closed shape, "so a runner cannot silently ignore
a field": every handler here refuses a case with a field it does not know or
without one it needs. The protocol is in `inventory.py`; this module only reads
the layouts, builds the scripted policy the README describes, and compares.

A handler returns on agreement and raises on disagreement (the runner counts
any exception as a FAIL).
"""

from typing import List, Optional

from . import inventory as INV

BINDING_FIELDS = {"device_id", "identity_hex", "capabilities"}
BINDING_OPTIONAL = {"replacement_predecessor_hex"}
STATEMENT_FIELDS = ("issuer_key_id", "account_handle", "inventory_generation", "active",
                    "revocation_floor_generation", "revoked")


class VectorMismatch(AssertionError):
    pass


def _closed(obj, required, optional=frozenset(), what="object"):
    if not isinstance(obj, dict):
        raise VectorMismatch(f"{what} is not an object")
    keys = set(obj)
    if not required <= keys or keys - required - set(optional):
        raise VectorMismatch(f"{what} fields {sorted(keys)} do not match the closed shape")


def _int(value, what):
    if not isinstance(value, int) or isinstance(value, bool):
        raise VectorMismatch(f"{what} is not an integer")
    return value


# ------------------------------------------------------------ JSON <-> values

def binding_from_json(obj) -> INV.DeviceBinding:
    """"A binding is `{"device_id", "identity_hex", "capabilities"}` and, when
    it names a predecessor, `"replacement_predecessor_hex"`."""
    _closed(obj, BINDING_FIELDS, BINDING_OPTIONAL, "binding")
    pred = obj.get("replacement_predecessor_hex")
    return INV.DeviceBinding(_int(obj["device_id"], "device_id"), bytes.fromhex(obj["identity_hex"]),
                             _int(obj["capabilities"], "capabilities"),
                             None if pred is None else bytes.fromhex(pred))


def binding_to_json(b: INV.DeviceBinding) -> dict:
    out = {"device_id": b.device_id, "identity_hex": b.identity_public_key.hex(),
           "capabilities": b.capabilities}
    if b.replacement_predecessor is not None:
        out["replacement_predecessor_hex"] = b.replacement_predecessor.hex()
    return out


def statement_from_json(case) -> INV.Statement:
    """The fields of an `inventory-statements-v1.json` case. `account_handle`
    is "a JSON string, whose UTF-8 bytes are the handle"; `revoked` entries are
    `{"binding", "terminal_generation"}`."""
    if not isinstance(case["active"], list) or not isinstance(case["revoked"], list):
        raise VectorMismatch("active and revoked are lists")
    revoked = []
    for entry in case["revoked"]:
        _closed(entry, {"binding", "terminal_generation"}, what="revoked entry")
        revoked.append(INV.Revocation(binding_from_json(entry["binding"]),
                                      _int(entry["terminal_generation"], "terminal_generation")))
    account = case["account_handle"]
    if not isinstance(account, str):
        raise VectorMismatch("account_handle is not a JSON string")
    return INV.Statement(_int(case["issuer_key_id"], "issuer_key_id"), account.encode("utf-8"),
                         _int(case["inventory_generation"], "inventory_generation"),
                         tuple(binding_from_json(b) for b in case["active"]),
                         _int(case["revocation_floor_generation"], "revocation_floor_generation"),
                         tuple(revoked))


def statement_to_json(s: INV.Statement) -> dict:
    return {"issuer_key_id": s.issuer_key_id,
            "account_handle": bytes(s.account_handle).decode("utf-8"),
            "inventory_generation": s.inventory_generation,
            "active": [binding_to_json(b) for b in s.active],
            "revocation_floor_generation": s.revocation_floor_generation,
            "revoked": [{"binding": binding_to_json(r.binding), "terminal_generation": r.terminal_generation}
                        for r in s.revoked]}


# ------------------------------------------------------------------ handlers

def h_statements(case):
    """`inventory-statements-v1.json`: "An encoder given the fields produces the
    bytes, and a decoder given the bytes returns the fields.\""""
    _closed(case, {"id", "unsigned_hex", *STATEMENT_FIELDS}, what="case")
    s = statement_from_json(case)
    encoded = INV.encode_unsigned(s)
    if encoded.hex() != case["unsigned_hex"]:
        raise VectorMismatch(f"encoder: expected {case['unsigned_hex'][:64]}.. got {encoded.hex()[:64]}..")
    decoded = INV.decode_unsigned(bytes.fromhex(case["unsigned_hex"]))
    want = {k: case[k] for k in STATEMENT_FIELDS}
    if statement_to_json(decoded) != want:
        raise VectorMismatch("decoder: the fields differ from the case's")


def h_decode_refusals(case):
    """`inventory-decode-refusals-v1.json`: "`unsigned_hex` is refused by the
    unsigned decoder." `rule` is a description, and is not compared."""
    _closed(case, {"id", "rule", "unsigned_hex"}, what="case")
    try:
        INV.decode_unsigned(bytes.fromhex(case["unsigned_hex"]))
    except INV.DecodeFailure:
        return
    raise VectorMismatch(f"accepted; expected a decode refusal ({case['rule']})")


def h_binding_commitments(case):
    """`inventory-binding-commitments-v1.json`: `commitment_hex` is
    `binding_commitment` of `binding`, or `null` where the binding has no
    encoding and no commitment."""
    _closed(case, {"id", "binding", "commitment_hex"}, what="case")
    b = binding_from_json(case["binding"])
    try:
        got = INV.binding_commitment(b).hex()
    except INV.DecodeFailure:
        got = None
    if got != case["commitment_hex"]:
        raise VectorMismatch(f"commitment: expected {case['commitment_hex']} got {got}")


class ScriptedPolicy(INV.Policy):
    """The README's scripted policy, recording every call as a hook-call
    string:

    - "An issuer resolves through the first entry of `issuers` whose
      `issuer_key_id` equals the statement's and whose `account_hex` is `null`
      or equals the account, to its `verification_key_hex`; if none does, the
      issuer is unbound."
    - "A generation is current for an account only if `fresh` lists that pair."
      Read as: exactly when (GAPS-12.md G12-01).
    - "A binding is refused when `refuse_every_binding` is true, or when it is
      the entry of the same identity as `refuse_binding.identity_hex` in the
      list `refuse_binding.status` (`active` or `revoked`) names." Read as:
      every entry of that identity in that list (G12-01).
    - "The statement is refused when `refuse_statement` is true."
    """

    FIELDS = {"issuers", "fresh", "refuse_binding", "refuse_every_binding", "refuse_statement"}

    def __init__(self, script):
        _closed(script, self.FIELDS, what="policy")
        self.issuers = []
        for entry in script["issuers"]:
            _closed(entry, {"issuer_key_id", "account_hex", "verification_key_hex"}, what="issuer")
            account = entry["account_hex"]
            self.issuers.append((_int(entry["issuer_key_id"], "issuer_key_id"),
                                 None if account is None else bytes.fromhex(account),
                                 bytes.fromhex(entry["verification_key_hex"])))
        self.fresh_pairs = set()
        for entry in script["fresh"]:
            _closed(entry, {"account_hex", "generation"}, what="fresh entry")
            self.fresh_pairs.add((bytes.fromhex(entry["account_hex"]), _int(entry["generation"], "generation")))
        rb = script["refuse_binding"]
        if rb is not None:
            _closed(rb, {"identity_hex", "status"}, what="refuse_binding")
            if rb["status"] not in ("active", "revoked"):
                raise VectorMismatch("refuse_binding.status is neither active nor revoked")
            rb = (bytes.fromhex(rb["identity_hex"]), rb["status"])
        self.refuse_binding = rb
        if not isinstance(script["refuse_every_binding"], bool) or not isinstance(script["refuse_statement"], bool):
            raise VectorMismatch("refuse_every_binding and refuse_statement are booleans")
        self.refuse_every_binding = script["refuse_every_binding"]
        self.refuse_statement = script["refuse_statement"]
        self.calls: List[str] = []
        self.statements_seen: List[INV.Statement] = []

    def issuer_key(self, issuer_key_id, account_handle) -> Optional[bytes]:
        self.calls.append(f"issuer:{issuer_key_id}:{account_handle.hex()}")
        for kid, account, key in self.issuers:
            if kid == issuer_key_id and (account is None or account == account_handle):
                return key
        return None

    def fresh(self, account_handle, generation) -> bool:
        self.calls.append(f"freshness:{account_handle.hex()}:{generation}")
        return (account_handle, generation) in self.fresh_pairs

    def accept_binding(self, binding, status) -> bool:
        pred = binding.replacement_predecessor
        self.calls.append("binding:%s:%d:%s:%d:%s" % ("A" if status == "active" else "R", binding.device_id,
                                                     binding.identity_public_key.hex(), binding.capabilities,
                                                     "-" if pred is None else pred.hex()))
        if self.refuse_every_binding:
            return False
        if self.refuse_binding is not None:
            identity, which = self.refuse_binding
            if which == status and identity == binding.identity_public_key:
                return False
        return True

    def accept_statement(self, statement) -> bool:
        self.calls.append("statement")
        self.statements_seen.append(statement)
        return not self.refuse_statement


def run_acceptance(case):
    """Returns (refusal, hook_calls, statement or None, policy)."""
    policy = ScriptedPolicy(case["policy"])
    signed = bytes.fromhex(case["signed_hex"])
    asked = bytes.fromhex(case["expected_account_hex"])
    try:
        s = INV.accept(signed, asked, policy)
    except INV.InventoryRefusal as e:
        return e.check, policy.calls, None, policy
    return None, policy.calls, s, policy


def h_acceptance(case):
    """`inventory-acceptance-v1.json`: a case passes only when the reader's
    `refusal` and `hook_calls` both equal the vector's. "An accepted statement
    is the decoded `signed_hex`": for an accepted case the statement returned,
    and the one the statement policy was given, re-encode to the preimage."""
    _closed(case, {"id", "signed_hex", "expected_account_hex", "policy", "refusal", "hook_calls"}, what="case")
    if case["refusal"] is not None and case["refusal"] not in INV.CHECKS:
        raise VectorMismatch(f"refusal {case['refusal']!r} is not one of the README's names")
    refusal, calls, s, policy = run_acceptance(case)
    if refusal != case["refusal"]:
        raise VectorMismatch(f"refusal: expected {case['refusal']} got {refusal}")
    if calls != case["hook_calls"]:
        raise VectorMismatch(f"hook_calls: expected {case['hook_calls']} got {calls}")
    if s is not None:
        preimage = bytes.fromhex(case["signed_hex"])[:-INV.SIGNATURE_LEN]
        if INV.encode_unsigned(s) != preimage or [INV.encode_unsigned(x) for x in policy.statements_seen] != [preimage]:
            raise VectorMismatch("the accepted statement is not the decoded signed_hex")


SCHEMAS = {
    "tacenta-inventory-statements-v1": h_statements,
    "tacenta-inventory-decode-refusals-v1": h_decode_refusals,
    "tacenta-inventory-binding-commitments-v1": h_binding_commitments,
    "tacenta-inventory-acceptance-v1": h_acceptance,
}
