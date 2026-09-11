"""Erasure code cases, from mlkem-braid.md "The erasure code". The field
arithmetic and interpolation are pinned by post-quantum/gf.json, inv.json and
interp.json (run as vectors); EC-04 reuses interp.json's values as chunk
elements. No vector exercises chunking, codewords or decoding."""

import itertools
import json
import os
import random

from _casekit import accepts, registry, rejects
from tacenta_reader import constants as K
from tacenta_reader import erasure, gf65536

CASES, case = registry()
EC = "mlkem-braid.md The erasure code"
# The vectors sit beside the reader in the clean-room layout, and two
# directories up in the repository layout; use whichever is present.
_READER_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VECTORS = next(
    candidate
    for candidate in (
        os.path.join(_READER_ROOT, "tacenta-test-vectors", "vectors"),
        os.path.join(_READER_ROOT, "..", "..", "vectors"),
    )
    if os.path.isdir(candidate)
)
R = random.Random(20260911)


def rnd(n):
    return bytes(R.randrange(256) for _ in range(n))


@case("EC-01 the table-driven multiply and inverse used by the coder equal the definitions (carry-less product mod 0x1100B; a^(2^16-2))",
      f"{EC}: Multiplication is the carry-less product ... Division by a nonzero a is multiplication by a^(2^16 - 2)")
def _():
    for a, b in [(0x8000, 2), (0xFFFF, 0xFFFF), (0x1234, 0x5678), (0, 7)] + [(R.randrange(65536), R.randrange(65536)) for _ in range(3000)]:
        assert gf65536.mul_fast(a, b) == gf65536.mul(a, b)
    for a in [1, 2, 0x8000, 0xFFFF] + [R.randrange(1, 65536) for _ in range(200)]:
        assert gf65536.inv_fast(a) == gf65536.inv(a)
    rejects(gf65536.inv_fast, 0, exc=gf65536.FieldError)


@case("EC-02 chunking: k = ceil(n/32), last chunk zero-padded, element j = bytes 2j, 2j+1 big-endian",
      f"{EC} Chunks: A value of n bytes is cut into k = ceil(n / 32) chunks ... the last padded with zero bytes")
def _():
    for n, k in ((0, 0), (1, 1), (32, 1), (33, 2), (96, 3), (192, 6), (1408, 44), (1536, 48)):
        v = rnd(n)
        ch = erasure.to_chunks(v)
        assert len(ch) == k == erasure.chunk_count(n)
        assert b"".join(ch)[:n] == v and set(b"".join(ch)[n:]) <= {0}
    c = bytes(range(32))
    assert erasure.elements(c)[0] == 0x0001 and erasure.elements(c)[15] == 0x1E1F
    assert erasure.from_elements(erasure.elements(c)) == c


@case("EC-03 systematic: codeword i < k is chunk_i", f"{EC} Codewords: For i < k the bytes are chunk_i")
def _():
    v = rnd(96)
    e = erasure.Encoder.for_value(v)
    assert [e.codeword(i) for i in range(3)] == erasure.to_chunks(v)


@case("EC-04 parity codeword element j is P_j(i), checked against interp.json's values and an independent Lagrange evaluation",
      f"{EC} Codewords: element j of the bytes is P_j(i), where P_j is the polynomial of degree below k through (t, element j of chunk_t)")
def _():
    with open(os.path.join(VECTORS, "post-quantum", "interp.json")) as f:
        vec = {v["id"]: v for v in json.load(f)["vectors"]}
    base = vec["at-a-lost-node"]["inputs"]
    assert base["nodes"] == "000000010002"          # nodes 0, 1, 2: the systematic positions of a 3-chunk value
    vals = gf65536.elements_from_bytes(bytes.fromhex(base["values"]))
    chunks = [v.to_bytes(2, "big") + bytes(30) for v in vals]
    e = erasure.Encoder(chunks)
    assert e.codeword(3)[:2].hex() == vec["at-a-lost-node"]["output"]
    assert e.codeword(0x4321)[:2].hex() == vec["far-from-the-nodes"]["output"]
    v = rnd(160)
    e = erasure.Encoder.for_value(v)
    ch = erasure.to_chunks(v)
    for i in (5, 6, 100, 0xFFFF):
        cw = erasure.elements(e.codeword(i))
        for j in (0, 7, 15):
            assert cw[j] == gf65536.interpolate(list(range(5)), [erasure.elements(c)[j] for c in ch], i)


@case("EC-05 decoding from any k held codewords recovers the value truncated to n (systematic, parity, mixed; Braid sizes and ragged sizes)",
      f"{EC} Decoding: With k codewords held at distinct indices ... The value is the k chunks in order, truncated to n bytes")
def _():
    for n in (1, 31, 33, 96, 192, 1408, 1536):
        v = rnd(n)
        e = erasure.Encoder.for_value(v)
        k = erasure.chunk_count(n)
        pools = [list(range(k)), list(range(k, 2 * k)), list(range(0, 2 * k, 2)), R.sample(range(3 * k + 3), k),
                 [0xFFFF - i for i in range(k)]]
        for idx in pools:
            d = erasure.Decoder(n)
            R.shuffle(idx)
            for i in idx:
                assert d.receive(i, e.codeword(i))
            assert d.complete() and d.value() == v, (n, idx[:4])
    v = rnd(96)
    e = erasure.Encoder.for_value(v)
    for subset in itertools.combinations(range(6), 3):
        d = erasure.Decoder(96)
        for i in subset:
            d.receive(i, e.codeword(i))
        assert d.value() == v


@case("EC-06 first copy wins: a later codeword at a held index is ignored even when its bytes differ",
      f"{EC} Decoding: a later one at an index it already holds is ignored, even when its bytes differ")
def _():
    v = rnd(96)
    e = erasure.Encoder.for_value(v)
    d = erasure.Decoder(96)
    assert d.receive(4, e.codeword(4))
    assert not d.receive(4, b"\xff" * 32)
    d.receive(1, e.codeword(1))
    d.receive(7, e.codeword(7))
    assert d.value() == v and d.held[0] == (4, e.codeword(4))
    # and a corrupt FIRST copy is binding: it is kept and the later good copy ignored
    d = erasure.Decoder(96)
    d.receive(4, b"\x00" * 32)
    assert not d.receive(4, e.codeword(4))
    d.receive(1, e.codeword(1))
    d.receive(7, e.codeword(7))
    assert d.value() != v


@case("EC-07 once k codewords are held every further one is ignored",
      f"{EC} Decoding: once it holds k codewords every further one is ignored")
def _():
    v = rnd(64)
    e = erasure.Encoder.for_value(v)
    d = erasure.Decoder(64)
    d.receive(9, e.codeword(9))
    d.receive(2, e.codeword(2))
    assert not d.receive(0, b"\x13" * 32) and not d.receive(1, e.codeword(1))
    assert len(d.held) == 2 and d.value() == v


@case("EC-08 a decoder for zero bytes holds the empty value before any codeword; an incomplete decoder holds none",
      f"{EC} Decoding: A decoder for zero bytes holds the empty value before any codeword arrives")
def _():
    assert erasure.Decoder(0).value() == b"" and erasure.Decoder(0).complete()
    assert not erasure.Decoder(0).receive(0, bytes(32))
    d = erasure.Decoder(96)
    d.receive(0, bytes(32))
    assert d.value() is None


@case("EC-09 encoder issues 0, 1, 2 ... and nothing after index 65,535 (exhausted)",
      f"{EC} Codewords: Once it has issued index 65,535 it issues nothing more; Encoder lifetime")
def _():
    e = erasure.Encoder.for_value(rnd(96))
    assert [e.issue()[0] for _ in range(4)] == [0, 1, 2, 3]
    e = erasure.Encoder(e.chunks, next_index=K.U16_MAX - 1)
    assert e.issue()[0] == K.U16_MAX - 1 and not e.exhausted
    i, cw = e.issue()
    assert i == K.U16_MAX and cw == e.codeword(K.U16_MAX) and e.exhausted and e.next == K.U16_MAX
    assert e.issue() is None and e.issue() is None


@case("EC-10 index and chunk widths: an index outside 16 bits or a chunk not 32 bytes is not a codeword",
      f"{EC} Codewords: A codeword is a 16-bit index i ... and 32 bytes")
def _():
    d = erasure.Decoder(32)
    rejects(d.receive, 0x10000, bytes(32), exc=ValueError)
    rejects(d.receive, 0, bytes(31), exc=ValueError)
    rejects(erasure.Encoder.for_value(b"x").codeword, -1, exc=ValueError)
