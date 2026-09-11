"""The Braid's erasure code, from mlkem-braid.md, "The erasure code".

Chunks. "A 32-byte chunk is 16 elements, element j being bytes 2j and 2j + 1
read big-endian. A value of n bytes is cut into k = ceil(n / 32) chunks ...
the last padded with zero bytes."

Codewords. "For i < k the bytes are chunk_i. For i >= k, element j of the
bytes is P_j(i), where P_j is the polynomial of degree below k through the
points (t, element j of chunk_t)." An encoder issues 0, 1, 2, ... and "once
it has issued index 65,535 it issues nothing more".

Decoding. The receiver knows n. "It keeps the first codeword it receives at
each index; a later one at an index it already holds is ignored, even when
its bytes differ, and once it holds k codewords every further one is
ignored." Missing chunk t is recovered by Lagrange interpolation at t over the
held indices; the value is the k chunks truncated to n bytes. "A decoder for
zero bytes holds the empty value before any codeword arrives."
"""

from typing import List, Optional, Tuple

from . import constants as K
from .gf65536 import inv_fast as _inv
from .gf65536 import mul_fast as _mul


def chunk_count(n: int) -> int:
    return -(-n // K.CHUNK_BYTES)


def to_chunks(value: bytes) -> List[bytes]:
    k = chunk_count(len(value))
    padded = bytes(value) + bytes(k * K.CHUNK_BYTES - len(value))
    return [padded[K.CHUNK_BYTES * t:K.CHUNK_BYTES * (t + 1)] for t in range(k)]


def elements(chunk: bytes) -> List[int]:
    if len(chunk) != K.CHUNK_BYTES:
        raise ValueError("a chunk is 32 bytes")
    return [int.from_bytes(chunk[2 * j:2 * j + 2], "big") for j in range(16)]


def from_elements(els: List[int]) -> bytes:
    return b"".join(e.to_bytes(2, "big") for e in els)


def _inv_denominators(nodes: List[int]) -> List[int]:
    """1 / prod_{l != m} (x_m + x_l), for each m."""
    out = []
    for m, xm in enumerate(nodes):
        d = 1
        for l, xl in enumerate(nodes):
            if l != m:
                d = _mul(d, xm ^ xl)
        out.append(_inv(d))
    return out


def _basis_at(nodes: List[int], inv_den: List[int], x: int) -> List[int]:
    """L_m(x) = prod_{l != m} (x + x_l) / (x_m + x_l), for each m."""
    k = len(nodes)
    diffs = [x ^ xl for xl in nodes]
    prefix = [1] * (k + 1)
    for i in range(k):
        prefix[i + 1] = _mul(prefix[i], diffs[i])
    suffix = [1] * (k + 1)
    for i in range(k - 1, -1, -1):
        suffix[i] = _mul(suffix[i + 1], diffs[i])
    return [_mul(_mul(prefix[m], suffix[m + 1]), inv_den[m]) for m in range(k)]


def _combine(els: List[List[int]], basis: List[int]) -> bytes:
    out = []
    for j in range(16):
        acc = 0
        for m, b in enumerate(basis):
            if b:
                acc ^= _mul(els[m][j], b)
        out.append(acc)
    return from_elements(out)


class Encoder:
    """An erasure encoder: its chunks, the next index to issue, and whether it
    is exhausted (session-persistence.md, Erasure coder sub-formats)."""

    def __init__(self, chunks: List[bytes], next_index: int = 0, exhausted: bool = False):
        for c in chunks:
            if len(c) != K.CHUNK_BYTES:
                raise ValueError("a chunk is 32 bytes")
        # mlkem-braid.md, Codewords (pass 5): "An encoder holds at most the
        # first 65,536 chunks of its value: all k of them when k is at most
        # 65,536, and chunk_0 to chunk_65535 otherwise." So no encoder holds
        # more; for_value keeps only those. Pass 4 held every chunk, because
        # the text then left which chunks unspecified (GAPS-4.md).
        if len(chunks) > K.MAX_CODEWORDS:
            raise ValueError("an encoder holds at most the first 65,536 chunks of its value")
        self.chunks = [bytes(c) for c in chunks]
        self.next = next_index
        self.exhausted = exhausted
        self._els = None
        self._inv_den = None

    @classmethod
    def for_value(cls, value: bytes) -> "Encoder":
        """"An encoder over a value of more than 65,536 chunks ... is not
        refused. It holds chunk_0 to chunk_65535 and no chunk after them.\""""
        return cls(to_chunks(value)[:K.MAX_CODEWORDS])

    def __eq__(self, other):
        return (isinstance(other, Encoder) and self.chunks == other.chunks
                and self.next == other.next and self.exhausted == other.exhausted)

    def __repr__(self):
        return f"Encoder(k={len(self.chunks)}, next={self.next}, exhausted={self.exhausted})"

    def codeword(self, i: int) -> bytes:
        if not 0 <= i <= K.U16_MAX:
            raise ValueError("a codeword index is 16 bits")
        k = len(self.chunks)
        if i < k:
            return self.chunks[i]
        if k == 0:
            return bytes(K.CHUNK_BYTES)
        if self._els is None:
            self._els = [elements(c) for c in self.chunks]
            self._inv_den = _inv_denominators(list(range(k)))
        return _combine(self._els, _basis_at(list(range(k)), self._inv_den, i))

    def issue(self) -> Optional[Tuple[int, bytes]]:
        """The next codeword to send, or None once exhausted (Encoder lifetime)."""
        if self.exhausted:
            return None
        i = self.next
        cw = self.codeword(i)
        if i == K.U16_MAX:
            self.exhausted = True
        else:
            self.next = i + 1
        return i, cw


class Decoder:
    """An erasure decoder for a value of `size` bytes."""

    def __init__(self, size: int, held: Optional[List[Tuple[int, bytes]]] = None):
        if size < 0:
            raise ValueError("size is a byte count")
        self.size = size
        self.needed = chunk_count(size)
        self.held: List[Tuple[int, bytes]] = [(int(i), bytes(d)) for i, d in (held or [])]

    def __deepcopy__(self, memo):
        return Decoder(self.size, list(self.held))

    def __eq__(self, other):
        return (isinstance(other, Decoder) and self.size == other.size
                and self.needed == other.needed and self.held == other.held)

    def __repr__(self):
        return f"Decoder(size={self.size}, needed={self.needed}, held={len(self.held)})"

    def receive(self, index: int, data: bytes) -> bool:
        """Offer a codeword. Returns whether it was kept."""
        if not 0 <= index <= K.U16_MAX or len(data) != K.CHUNK_BYTES:
            raise ValueError("a codeword is a 16-bit index and 32 bytes")
        if len(self.held) >= self.needed:
            return False                       # holds k: every further one ignored
        seen = getattr(self, "_seen", None)
        if seen is None or len(seen) != len(self.held):
            seen = self._seen = {i for i, _ in self.held}
        if index in seen:
            return False                       # first copy wins
        self.held.append((index, bytes(data)))
        seen.add(index)
        return True

    def complete(self) -> bool:
        return len(self.held) >= self.needed

    def value(self) -> Optional[bytes]:
        if self.needed == 0:
            return b""
        if not self.complete():
            return None
        k = self.needed
        by_index = dict(self.held)
        nodes = [i for i, _ in self.held]
        els = inv_den = None
        chunks = []
        for t in range(k):
            if t in by_index:
                chunks.append(by_index[t])
                continue
            if els is None:
                els = [elements(d) for _, d in self.held]
                inv_den = _inv_denominators(nodes)
            chunks.append(_combine(els, _basis_at(nodes, inv_den, t)))
        return b"".join(chunks)[:self.size]
