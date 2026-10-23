//! SHA-256 (FIPS 180-4), for byte-string messages.
//!
//! Incremental: `Sha256::new`, `update` any number of times, `finalize`.
//! HMAC and the AEAD's tag hash concatenations that are never built, by
//! feeding their parts in turn. `sha256` is the one-shot form.
//!
//! `update` absorbs one byte at a time and compresses whenever the 64-byte
//! buffer fills. That is slower than copying whole blocks, and it is the
//! shape the refinement proof's auxiliary specification states
//! (`PLAN.md`, "HMAC hashes streams").
//!
//! Every branch and every index is on a length or a loop counter, never on
//! message bytes (`PLAN.md`, constant-time requirements).

/// The 64 round constants `K_0 … K_63` (FIPS 180-4 §4.2.2): the first 32
/// bits of the fractional parts of the cube roots of the first 64 primes.
/// `tests/sha256.rs` recomputes them from that definition.
pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// The initial hash value `H^(0)` (FIPS 180-4 §5.3.3): the first 32 bits of
/// the fractional parts of the square roots of the first 8 primes.
pub const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// `Ch(x, y, z)` (FIPS 180-4 (4.2)).
fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (!x & z)
}

/// `Maj(x, y, z)` (FIPS 180-4 (4.3)).
fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

/// `Σ0^{256}(x)` (FIPS 180-4 (4.4)).
fn big_sigma0(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}

/// `Σ1^{256}(x)` (FIPS 180-4 (4.5)).
fn big_sigma1(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}

/// `σ0^{256}(x)` (FIPS 180-4 (4.6)).
fn small_sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}

/// `σ1^{256}(x)` (FIPS 180-4 (4.7)).
fn small_sigma1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

/// The message schedule `W_0 … W_63` of one block (FIPS 180-4 §6.2.2,
/// step 1). Words are big-endian (§3.1).
fn schedule(block: &[u8; 64]) -> [u32; 64] {
    let mut w = [0u32; 64];
    let mut t = 0;
    while t < 16 {
        w[t] = ((block[4 * t] as u32) << 24)
            | ((block[4 * t + 1] as u32) << 16)
            | ((block[4 * t + 2] as u32) << 8)
            | (block[4 * t + 3] as u32);
        t += 1;
    }
    while t < 64 {
        w[t] = small_sigma1(w[t - 2])
            .wrapping_add(w[t - 7])
            .wrapping_add(small_sigma0(w[t - 15]))
            .wrapping_add(w[t - 16]);
        t += 1;
    }
    w
}

/// One application of the compression function: `H^(i)` from `H^(i-1)`
/// and the block `M^(i)` (FIPS 180-4 §6.2.2, steps 1–4).
pub(crate) fn compress(h: &[u32; 8], block: &[u8; 64]) -> [u32; 8] {
    let w = schedule(block);
    let mut a = h[0];
    let mut b = h[1];
    let mut c = h[2];
    let mut d = h[3];
    let mut e = h[4];
    let mut f = h[5];
    let mut g = h[6];
    let mut hh = h[7];
    let mut t = 0;
    while t < 64 {
        let t1 = hh
            .wrapping_add(big_sigma1(e))
            .wrapping_add(ch(e, f, g))
            .wrapping_add(K[t])
            .wrapping_add(w[t]);
        let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));
        hh = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
        t += 1;
    }
    [
        a.wrapping_add(h[0]),
        b.wrapping_add(h[1]),
        c.wrapping_add(h[2]),
        d.wrapping_add(h[3]),
        e.wrapping_add(h[4]),
        f.wrapping_add(h[5]),
        g.wrapping_add(h[6]),
        hh.wrapping_add(h[7]),
    ]
}

/// An incremental SHA-256 computation.
///
/// Invariant, kept by every method: `buf_len < 64`; `state` is the
/// compression function folded from `H0` over the complete blocks absorbed
/// so far; `buf[..buf_len]` holds the bytes after them; `total` is the
/// number of bytes absorbed, modulo `2^64`.
#[derive(Clone, Copy)]
pub struct Sha256 {
    state: [u32; 8],
    buf: [u8; 64],
    buf_len: usize,
    total: u64,
}

impl Sha256 {
    pub fn new() -> Sha256 {
        Sha256 { state: H0, buf: [0u8; 64], buf_len: 0, total: 0 }
    }

    /// Absorb one byte.
    fn absorb(&mut self, byte: u8) {
        self.buf[self.buf_len] = byte;
        self.buf_len += 1;
        self.total = self.total.wrapping_add(1);
        if self.buf_len == 64 {
            self.state = compress(&self.state, &self.buf);
            self.buf_len = 0;
        }
    }

    pub fn update(&mut self, data: &[u8]) {
        let mut i = 0;
        while i < data.len() {
            self.absorb(data[i]);
            i += 1;
        }
    }

    /// Pad (FIPS 180-4 §5.1.1) and compress the final block or two, then
    /// write `H^(N)` big-endian (§6.2.2, after step 4). The length field is
    /// the bit length `8 · total`, which is exact whenever the message is
    /// shorter than `2^61` bytes, as §5.1.1's `ℓ < 2^64` requires.
    pub fn finalize(&self) -> [u8; 32] {
        let bit_len = self.total.wrapping_mul(8);
        let mut state = self.state;
        let mut buf = self.buf;
        let mut n = self.buf_len;
        buf[n] = 0x80;
        n += 1;
        if n > 56 {
            while n < 64 {
                buf[n] = 0;
                n += 1;
            }
            state = compress(&state, &buf);
            n = 0;
        }
        while n < 56 {
            buf[n] = 0;
            n += 1;
        }
        let mut j = 0;
        while j < 8 {
            buf[56 + j] = (bit_len >> (56 - 8 * j)) as u8;
            j += 1;
        }
        state = compress(&state, &buf);
        let mut out = [0u8; 32];
        let mut i = 0;
        while i < 8 {
            out[4 * i] = (state[i] >> 24) as u8;
            out[4 * i + 1] = (state[i] >> 16) as u8;
            out[4 * i + 2] = (state[i] >> 8) as u8;
            out[4 * i + 3] = state[i] as u8;
            i += 1;
        }
        out
    }
}

/// SHA-256 of `data` (FIPS 180-4 §6.2).
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(data);
    h.finalize()
}
