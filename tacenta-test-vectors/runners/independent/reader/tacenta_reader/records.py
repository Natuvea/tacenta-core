"""Identity records, the identity pair digest and the initiator's expectation
(pass 14).

From identities-and-devices.md, The identity pair digest and The verification
number, and session-establishment.md, Records, expectations and attribution.
Nothing here is taken from a vector's bytes.

- `identity_pair_digest(k1, k2)` and `verification_number(digest)`;
- `Record`, a contact's two sets, *current* and *retired*;
- `classify(key, record)`: *same*, *new* or *retired*, or a refusal;
- `lookup(key, records)`: a contact's, ambiguous, a retired key or
  unattributed, with the contacts the key is retired for and the records
  skipped as malformed;
- `Known` and `FirstContact`, the initiator's two expectations, with
  `check_expectation_wellformed` (`MalformedRecord`, before any check of
  Sending the initial message) and `check_bundle_identity` (the check against
  the expectation, which applies the identity-key rule to the key first).

The page fixes the results and leaves names and signatures to the
implementation: "Their results are fixed here; their names and signatures are
not."
"""

import hashlib
from dataclasses import dataclass, field
from typing import FrozenSet, Iterable, List, Optional, Sequence, Tuple, Union

from . import constants as K
from .curve25519 import is_identity_key
from .wire import DecodeError, InvalidIdentityKey, is_canonical_curve_key

# identities-and-devices.md, The identity pair digest:
#   PAIR_DIGEST_LABEL = "Tacenta:identity:pair-digest:v1" || 0xFF     -- 32 bytes
PAIR_DIGEST_LABEL = K.PAIR_DIGEST_LABEL

SAME, NEW, RETIRED = "same", "new", "retired"

UNATTRIBUTED, CONTACT, AMBIGUOUS, RETIRED_KEY = "unattributed", "contact", "ambiguous", "retired-key"


# ---------------------------------------------------------------- refusals

class MalformedRecord(Exception):
    """"it refuses the classification as a malformed record (`MalformedRecord`),
    even if `k` matches another member. That refusal reports the party's own
    record, never a peer's bytes." Also the refusal of a malformed expectation
    (Records, expectations and attribution, The initiator)."""


class ExpectationRefused(Exception):
    """A bundle whose identity key the initiator's expectation refuses
    (error-handling.md: "a bundle whose identity key the initiator's
    expectation refuses, as retired or unexpected")."""


class RetiredIdentity(ExpectationRefused):
    """`RetiredIdentity`."""


class UnexpectedIdentity(ExpectationRefused):
    """`UnexpectedIdentity`."""


# ------------------------------------------------------ the presented key

def admit_presented_key(k: bytes) -> bytes:
    """"Before anything else, `k` must be an identity key:
    - if `k` is not the canonical encoding of a curve public key ..., the
      classification refuses it as `DecodeEC` refuses such a key (a decode
      failure);
    - if `k` is canonical but not an identity key, the classification refuses it
      as an invalid identity key."

    The same two refusals, in the same order, are the pair digest's ("a key
    whose bit 255 is set, or whose value ... is at least p ..., is refused as
    `DecodeEC` refuses it ...: a decode failure; a canonical key that is not an
    identity key is refused as an invalid identity key")."""
    k = bytes(k)
    if not is_canonical_curve_key(k):
        raise DecodeError("the presented key is not the canonical encoding of a curve public key")
    if not is_identity_key(k):
        raise InvalidIdentityKey("the presented key is not an identity key")
    return k


# ------------------------------------------------------- the pair digest

def identity_pair_digest(k1: bytes, k2: bytes) -> bytes:
    """identities-and-devices.md, The identity pair digest.

        refuse unless k1 and k2 are identity keys
        (lo, hi) = (k1, k2) if k1 <= k2, else (k2, k1)
        return SHA-256(PAIR_DIGEST_LABEL || lo || hi)

    "`k1 <= k2` compares the keys as strings of unsigned bytes, byte 0 first,
    and the first byte that differs decides." Python's `bytes` comparison is
    exactly that. "Equal keys are allowed." "It refuses nothing else. When both
    keys would be refused, either refusal conforms": this reader checks `k1`
    whole, then `k2`."""
    k1 = admit_presented_key(k1)
    k2 = admit_presented_key(k2)
    lo, hi = (k1, k2) if k1 <= k2 else (k2, k1)
    return hashlib.sha256(PAIR_DIGEST_LABEL + lo + hi).digest()


def verification_number(digest: bytes) -> str:
    """identities-and-devices.md, The verification number:

        n = digest read as an unsigned big-endian integer
        return n mod 10^60, as the ASCII digits 0 to 9, most significant first,
               left-padded with '0' to 60 digits

    The page applies it to a digest; it states no length for the input, and
    this reader takes the 32 bytes the digest is (G14-04)."""
    digest = bytes(digest)
    if len(digest) != 32:
        raise ValueError("a digest is 32 bytes")
    n = int.from_bytes(digest, "big") % 10 ** K.VERIFICATION_NUMBER_DIGITS
    return str(n).rjust(K.VERIFICATION_NUMBER_DIGITS, "0")


def verification_number_groups(number: str) -> List[str]:
    """"The digits may be laid out in twelve groups of five." Layout only: it
    does not change the digits."""
    assert len(number) == K.VERIFICATION_NUMBER_DIGITS
    return [number[i:i + 5] for i in range(0, len(number), 5)]


# ------------------------------------------------------------------ records

@dataclass(frozen=True)
class Record:
    """"For each contact, a party's record is two finite sets of 32-byte keys,
    each the canonical encoding of a curve public key ...: current ... retired".
    "A list given for a set denotes the set of its members, and duplicates are
    ignored." The members are kept as given; whether they are canonical is
    checked where the page checks it (classification; a malformed
    expectation), not here, since a record holding a non-canonical key is a
    thing the page says a party can hold and must be told about."""
    current: FrozenSet[bytes] = field(default_factory=frozenset)
    retired: FrozenSet[bytes] = field(default_factory=frozenset)

    @staticmethod
    def of(current: Iterable[bytes] = (), retired: Iterable[bytes] = ()) -> "Record":
        return Record(frozenset(bytes(k) for k in current), frozenset(bytes(k) for k in retired))

    @property
    def holds_record(self) -> bool:
        """"A party *holds a record* for a contact when either set is non-empty.\""""
        return bool(self.current) or bool(self.retired)

    def is_wellformed(self) -> bool:
        """Every member of both sets is a canonical encoding. "A member is held
        to the canonical encoding only, not to the identity-key rule"."""
        return all(is_canonical_curve_key(m) for m in self.current | self.retired)


def classify(k: bytes, record: Record) -> str:
    """session-establishment.md, Records, expectations and attribution,
    Classification.

    1. The presented key must be an identity key (decode failure, then invalid
       identity key).
    2. "It then checks every member of both sets. If any of them is not a
       canonical encoding, it refuses the classification as a malformed record
       (`MalformedRecord`), even if `k` matches another member."
    3. "*retired*, if it is in the retired set; otherwise *same*, if it is in the
       current set; otherwise *new*." Membership is equality of the 32 bytes.
    """
    k = admit_presented_key(k)
    if not record.is_wellformed():
        raise MalformedRecord("a member of the record is not the canonical encoding of a curve public key")
    if k in record.retired:
        return RETIRED
    if k in record.current:
        return SAME
    return NEW


@dataclass(frozen=True)
class LookupResult:
    """A lookup's result. "Wherever a lookup finds the key *retired* for a
    contact, that is reported alongside its result", and a malformed record
    "is skipped: it attributes nothing, and it is reported"."""
    attribution: str                     # UNATTRIBUTED, CONTACT, AMBIGUOUS or RETIRED_KEY
    contact: Optional[int]               # the contact, for CONTACT only
    retired_for: Tuple[int, ...]         # contacts the key is retired for, in record order
    malformed: Tuple[int, ...]           # records skipped as malformed, in record order
    same_for: Tuple[int, ...] = ()       # contacts the key is same for (not part of the vectors' result)


def lookup(k: bytes, records: Sequence[Record]) -> LookupResult:
    """session-establishment.md, Records, expectations and attribution, Lookup.

    "A key is looked up by classifying it against every record the party
    holds. A key the classification refuses as a decode failure or as an
    invalid identity key refuses the lookup in the same way, whether or not the
    party holds any record, and the lookup reports no record. A record whose
    classification is refused as a malformed record is skipped". The others
    decide: same for one, a contact's; same for more than one, ambiguous; same
    for none and retired for one or more, a retired key; otherwise
    unattributed.

    `records[n]` is contact n's record. A record whose two sets are both empty
    is one "it holds no record for": it classifies every key as *new* and adds
    nothing, so it may be passed or left out."""
    k = admit_presented_key(k)            # refuses the lookup, with no record reported
    same, retired, malformed = [], [], []
    for n, record in enumerate(records):
        try:
            cls = classify(k, record)
        except MalformedRecord:
            malformed.append(n)
            continue
        if cls == SAME:
            same.append(n)
        elif cls == RETIRED:
            retired.append(n)
    if len(same) == 1:
        attribution, contact = CONTACT, same[0]
    elif len(same) > 1:
        attribution, contact = AMBIGUOUS, None
    elif retired:
        attribution, contact = RETIRED_KEY, None
    else:
        attribution, contact = UNATTRIBUTED, None
    return LookupResult(attribution, contact, tuple(retired), tuple(malformed), tuple(same))


def attributed_contact(peer_identity: bytes, records: Sequence[Record]) -> Optional[int]:
    """Attribution: "A session is a contact's only when a lookup of its peer
    identity key finds it that contact's", against the records as they stand
    whenever a plaintext is shown or the session is used. None for a session
    that is no contact's (ambiguous, a retired key, or unattributed)."""
    result = lookup(peer_identity, records)
    return result.contact if result.attribution == CONTACT else None


# ------------------------------------------------------------ expectations

@dataclass(frozen=True)
class Known:
    """"*known*: the record of the contact she means to reach, which she
    selects herself. The record is non-empty"."""
    record: Record


@dataclass(frozen=True)
class FirstContact:
    """"*first contact*: for a peer she holds no record for. It carries all her
    records.\""""
    records: Tuple[Record, ...] = ()


Expectation = Union[Known, FirstContact]


def check_expectation_wellformed(expectation: Expectation) -> None:
    """"She refuses an expectation as a malformed record (`MalformedRecord`),
    before any check of Sending the initial message, when it holds a
    non-canonical key, in the record under *known* or in any of her records
    under *first contact*, or when it is *known* with a record whose two sets
    are both empty.\""""
    if isinstance(expectation, Known):
        if not expectation.record.holds_record:
            raise MalformedRecord("a known expectation whose record is empty")
        if not expectation.record.is_wellformed():
            raise MalformedRecord("the known record holds a non-canonical key")
        return
    if isinstance(expectation, FirstContact):
        for n, record in enumerate(expectation.records):
            if not record.is_wellformed():
                raise MalformedRecord(f"record {n} holds a non-canonical key")
        return
    raise TypeError("an initiator establishes only with an expectation, known or first contact")


def check_bundle_identity(expectation: Expectation, ikb: bytes) -> None:
    """The check of the bundle's identity key against her expectation.

    - "under *known*, by classifying it against that record. *Retired* is
      refused as a retired identity (`RetiredIdentity`). *New* is refused as an
      unexpected identity (`UnexpectedIdentity`). *Same* goes on."
    - "under *first contact*, by looking it up in her records: a key the lookup
      finds a contact's, or ambiguous, is refused as an unexpected identity
      (`UnexpectedIdentity`) ... That holds even when it is also *retired* for
      another contact. A retired key (*same* for no contact) is refused as a
      retired identity (`RetiredIdentity`). An unattributed key goes on."

    "Either way the check applies the identity-key rule to the key first, so a
    key that is not an identity key is refused as an invalid identity key"."""
    if isinstance(expectation, Known):
        cls = classify(ikb, expectation.record)
        if cls == RETIRED:
            raise RetiredIdentity("the bundle's identity key is retired in the record")
        if cls == NEW:
            raise UnexpectedIdentity("the bundle's identity key is new in the record")
        return
    if isinstance(expectation, FirstContact):
        result = lookup(ikb, expectation.records)
        if result.attribution in (CONTACT, AMBIGUOUS):
            raise UnexpectedIdentity("the bundle's identity key is a recorded contact's")
        if result.attribution == RETIRED_KEY:
            raise RetiredIdentity("the bundle's identity key is a retired key")
        return
    raise TypeError("an initiator establishes only with an expectation, known or first contact")
