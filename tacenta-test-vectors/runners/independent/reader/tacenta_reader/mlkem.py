# PROJECT-CONTROLLED DRY RUN. NOT INDEPENDENT EVIDENCE. It does not close or reclassify the open item.
"""PROJECT-CONTROLLED DRY RUN. NOT INDEPENDENT EVIDENCE. It does not close or reclassify the open item.

ML-KEM-1024 as FIPS 203 defines it (parameter set of Table 2: k = 4, eta1 = 2,
eta2 = 2, du = 11, dv = 5), written from the algorithms the specification names:

- `keygen_internal(d, z)`   ML-KEM.KeyGen_internal, Algorithm 16 (via K-PKE.KeyGen, Algorithm 13)
- `encaps_internal(ek, m)`  ML-KEM.Encaps_internal, Algorithm 17 (via K-PKE.Encrypt, Algorithm 14)
- `decaps_internal(dk, c)`  ML-KEM.Decaps_internal, Algorithm 18 (via K-PKE.Decrypt, Algorithm 15)
- `ek_modulus_check`, `dk_hash_check`  the checks of FIPS 203 sections 7.2 and 7.3

The page that calls for it is session-establishment.md, "ML-KEM-1024 (FIPS 203)",
and session-persistence.md, "Prekey store". The page names the algorithms and
leaves their internals to the standard. This file is a reading of the standard
as the author knew it: the standard text was not available in the directory,
so the helper functions (SampleNTT, SamplePolyCBD, NTT, ByteEncode, Compress)
are written from the author's recall of FIPS 203, and the NIST known-answer
vectors named in RECORD.md section 4 are the check on that recall.

Python 3 standard library only. Not constant-time, not fast: it exists to
compute values, never to protect a key.
"""

import hashlib

Q = 3329
N = 256
K = 4
ETA1 = 2
ETA2 = 2
DU = 11
DV = 5

EK_BYTES = 384 * K + 32          # 1,568
DK_PKE_BYTES = 384 * K           # 1,536
DK_BYTES = 768 * K + 96          # 3,168
CT_BYTES = 32 * (DU * K + DV)    # 1,568
CT1_BYTES = 32 * DU * K          # 1,408
CT2_BYTES = 32 * DV              # 160


def _bitrev7(i):
    r = 0
    for _ in range(7):
        r = (r << 1) | (i & 1)
        i >>= 1
    return r


ZETAS = [pow(17, _bitrev7(i), Q) for i in range(128)]
GAMMAS = [pow(17, 2 * _bitrev7(i) + 1, Q) for i in range(128)]


# ---- hash functions -------------------------------------------------------

def H(x):
    return hashlib.sha3_256(x).digest()


def G(x):
    return hashlib.sha3_512(x).digest()


def J(x):
    return hashlib.shake_256(x).digest(32)


def prf(eta, s, b):
    return hashlib.shake_256(s + bytes([b])).digest(64 * eta)


# ---- sampling -------------------------------------------------------------

def sample_ntt(seed34):
    """Algorithm 7. `seed34` is rho || j || i (34 bytes)."""
    # SHAKE128 has no incremental squeeze in hashlib; take a generous prefix
    # and extend it if the rejection sampling needs more.
    nbytes = 840
    while True:
        stream = hashlib.shake_128(seed34).digest(nbytes)
        a = []
        pos = 0
        while len(a) < N and pos + 3 <= len(stream):
            c0, c1, c2 = stream[pos], stream[pos + 1], stream[pos + 2]
            pos += 3
            d1 = c0 + 256 * (c1 % 16)
            d2 = (c1 // 16) + 16 * c2
            if d1 < Q:
                a.append(d1)
            if d2 < Q and len(a) < N:
                a.append(d2)
        if len(a) == N:
            return a
        nbytes *= 2


def sample_poly_cbd(eta, b):
    """Algorithm 8. `b` is 64 * eta bytes."""
    bits = []
    for byte in b:
        for t in range(8):
            bits.append((byte >> t) & 1)
    f = []
    for i in range(N):
        x = sum(bits[2 * i * eta + j] for j in range(eta))
        y = sum(bits[2 * i * eta + eta + j] for j in range(eta))
        f.append((x - y) % Q)
    return f


# ---- NTT ------------------------------------------------------------------

def ntt(f):
    f = list(f)
    i = 1
    ln = 128
    while ln >= 2:
        for start in range(0, N, 2 * ln):
            zeta = ZETAS[i]
            i += 1
            for j in range(start, start + ln):
                t = (zeta * f[j + ln]) % Q
                f[j + ln] = (f[j] - t) % Q
                f[j] = (f[j] + t) % Q
        ln //= 2
    return f


def ntt_inv(f):
    f = list(f)
    i = 127
    ln = 2
    while ln <= 128:
        for start in range(0, N, 2 * ln):
            zeta = ZETAS[i]
            i -= 1
            for j in range(start, start + ln):
                t = f[j]
                f[j] = (t + f[j + ln]) % Q
                f[j + ln] = (zeta * (f[j + ln] - t)) % Q
        ln *= 2
    return [(x * 3303) % Q for x in f]


def multiply_ntts(f, g):
    h = [0] * N
    for i in range(128):
        a0, a1 = f[2 * i], f[2 * i + 1]
        b0, b1 = g[2 * i], g[2 * i + 1]
        gam = GAMMAS[i]
        h[2 * i] = (a0 * b0 + a1 * b1 % Q * gam) % Q
        h[2 * i + 1] = (a0 * b1 + a1 * b0) % Q
    return h


def poly_add(a, b):
    return [(x + y) % Q for x, y in zip(a, b)]


def poly_sub(a, b):
    return [(x - y) % Q for x, y in zip(a, b)]


# ---- encoding -------------------------------------------------------------

def byte_encode(d, f):
    """Algorithm 5."""
    acc = 0
    for i, v in enumerate(f):
        acc |= v << (d * i)
    return acc.to_bytes(32 * d, "little")


def byte_decode(d, b):
    """Algorithm 6."""
    acc = int.from_bytes(b, "little")
    mask = (1 << d) - 1
    m = Q if d == 12 else (1 << d)
    return [((acc >> (d * i)) & mask) % m for i in range(N)]


def compress(d, x):
    return (((x << (d + 1)) + Q) // (2 * Q)) % (1 << d)


def decompress(d, y):
    return ((Q * y << 1) + (1 << d)) // (1 << (d + 1))


def ek_modulus_check(ek_t):
    """FIPS 203 section 7.2: ByteEncode12(ByteDecode12(b)) == b for b = ek[0:1536]."""
    if len(ek_t) != DK_PKE_BYTES:
        return False
    for i in range(K):
        part = ek_t[384 * i:384 * (i + 1)]
        if byte_encode(12, byte_decode(12, part)) != part:
            return False
    return True


# ---- K-PKE ----------------------------------------------------------------

def _matrix(rho):
    return [[sample_ntt(rho + bytes([j, i])) for j in range(K)] for i in range(K)]


def kpke_keygen(d):
    """Algorithm 13. `d` is 32 bytes. Returns (ek_pke, dk_pke)."""
    rho_sigma = G(d + bytes([K]))
    rho, sigma = rho_sigma[:32], rho_sigma[32:]
    A = _matrix(rho)
    n = 0
    s = []
    for _ in range(K):
        s.append(sample_poly_cbd(ETA1, prf(ETA1, sigma, n)))
        n += 1
    e = []
    for _ in range(K):
        e.append(sample_poly_cbd(ETA1, prf(ETA1, sigma, n)))
        n += 1
    s_hat = [ntt(p) for p in s]
    e_hat = [ntt(p) for p in e]
    t_hat = []
    for i in range(K):
        acc = [0] * N
        for j in range(K):
            acc = poly_add(acc, multiply_ntts(A[i][j], s_hat[j]))
        t_hat.append(poly_add(acc, e_hat[i]))
    ek_pke = b"".join(byte_encode(12, p) for p in t_hat) + rho
    dk_pke = b"".join(byte_encode(12, p) for p in s_hat)
    return ek_pke, dk_pke


def kpke_encrypt(ek_pke, m, r):
    """Algorithm 14. Returns c1 || c2 (1,568 bytes)."""
    t_hat = [byte_decode(12, ek_pke[384 * i:384 * (i + 1)]) for i in range(K)]
    rho = ek_pke[384 * K:384 * K + 32]
    A = _matrix(rho)
    n = 0
    y = []
    for _ in range(K):
        y.append(sample_poly_cbd(ETA1, prf(ETA1, r, n)))
        n += 1
    e1 = []
    for _ in range(K):
        e1.append(sample_poly_cbd(ETA2, prf(ETA2, r, n)))
        n += 1
    e2 = sample_poly_cbd(ETA2, prf(ETA2, r, n))
    y_hat = [ntt(p) for p in y]
    u = []
    for i in range(K):
        acc = [0] * N
        for j in range(K):
            acc = poly_add(acc, multiply_ntts(A[j][i], y_hat[j]))
        u.append(poly_add(ntt_inv(acc), e1[i]))
    mu = [decompress(1, b) for b in byte_decode(1, m)]
    acc = [0] * N
    for j in range(K):
        acc = poly_add(acc, multiply_ntts(t_hat[j], y_hat[j]))
    v = poly_add(poly_add(ntt_inv(acc), e2), mu)
    c1 = b"".join(byte_encode(DU, [compress(DU, x) for x in p]) for p in u)
    c2 = byte_encode(DV, [compress(DV, x) for x in v])
    return c1 + c2


def kpke_decrypt(dk_pke, c):
    """Algorithm 15. Returns the 32-byte message."""
    c1 = c[:32 * DU * K]
    c2 = c[32 * DU * K:32 * (DU * K + DV)]
    u = [[decompress(DU, x) for x in byte_decode(DU, c1[32 * DU * i:32 * DU * (i + 1)])] for i in range(K)]
    v = [decompress(DV, x) for x in byte_decode(DV, c2)]
    s_hat = [byte_decode(12, dk_pke[384 * i:384 * (i + 1)]) for i in range(K)]
    acc = [0] * N
    for j in range(K):
        acc = poly_add(acc, multiply_ntts(s_hat[j], ntt(u[j])))
    w = poly_sub(v, ntt_inv(acc))
    return byte_encode(1, [compress(1, x) for x in w])


# ---- ML-KEM ---------------------------------------------------------------

def keygen_internal(d, z):
    """Algorithm 16. Returns (ek, dk)."""
    assert len(d) == 32 and len(z) == 32
    ek_pke, dk_pke = kpke_keygen(d)
    ek = ek_pke
    dk = dk_pke + ek + H(ek) + z
    return ek, dk


def encaps_internal(ek, m):
    """Algorithm 17. Returns (K, c)."""
    assert len(m) == 32
    k_r = G(m + H(ek))
    key, r = k_r[:32], k_r[32:]
    c = kpke_encrypt(ek, m, r)
    return key, c


def decaps_internal(dk, c):
    """Algorithm 18. Returns K. Implicit rejection: a ciphertext that does not
    re-encrypt to itself gives J(z || c), never an error."""
    assert len(dk) == DK_BYTES and len(c) == CT_BYTES
    dk_pke = dk[:384 * K]
    ek_pke = dk[384 * K:768 * K + 32]
    h = dk[768 * K + 32:768 * K + 64]
    z = dk[768 * K + 64:768 * K + 96]
    m2 = kpke_decrypt(dk_pke, c)
    k_r = G(m2 + h)
    key, r2 = k_r[:32], k_r[32:]
    k_bar = J(z + c)
    c2 = kpke_encrypt(ek_pke, m2, r2)
    return key if c2 == c else k_bar


def dk_hash_check(dk):
    """FIPS 203 section 7.3: the stored hash equals H of the ek inside dk."""
    if len(dk) != DK_BYTES:
        return False
    return dk[768 * K + 32:768 * K + 64] == H(dk[384 * K:768 * K + 32])


def braid_split(ek):
    """mlkem-braid.md, The KEM split: `header = rho (32) || H(ek) (32)`, with H
    over all of ek, and `ek_vector = ByteEncode12(t_hat)`, ek without rho.
    Returns (header, ek_vector)."""
    if len(ek) != EK_BYTES:
        raise ValueError("an encapsulation key is 1,568 bytes")
    rho = ek[384 * K:]
    return rho + H(ek), ek[:384 * K]

