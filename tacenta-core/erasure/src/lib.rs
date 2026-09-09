//! tacenta-erasure: Reed-Solomon erasure coding over GF(2^16).
//!
//! Written from tacenta-spec/protocol/mlkem-braid.md, which recommends this
//! code with a `w`-byte chunk carrying `w/2` field elements, and from the
//! executable model in tacenta-model (`Model.Gf65536`, `Model.Polynomial`).
//!
//! The ML-KEM Braid needs to send values of one and a half kilobytes through a
//! channel with room for tens of bytes, over a network an adversary is allowed
//! to drop and reorder. So a value is sent as an unbounded stream of codewords,
//! any `k` of which reconstruct it.
//!
//! ## Systematic, by evaluation
//!
//! The message is cut into `k` chunks. Each chunk position holds `w/2` field
//! elements, and position `j` across the chunks defines one polynomial: the one
//! of degree below `k` whose value at node `t` is chunk `t`'s element `j`.
//! Codeword `i` is every lane's polynomial evaluated at node `i`.
//!
//! Two things follow. Codewords `0..k` *are* the message chunks, because the
//! message is what defines the values there, so in-order delivery costs no
//! arithmetic at all. And decoding is evaluation rather than coefficient
//! recovery: given any `k` codewords, the interpolant through them evaluated at
//! node `t` is chunk `t`. That is exactly `Model.Polynomial.interp_eq`, which is
//! proved, rather than a coefficient extraction that would need polynomial
//! division and is not.
//!
//! ## What is proved
//!
//! The field laws hold for every element: commutativity, associativity,
//! distributivity, and that every nonzero element inverts. Interpolation
//! reproduces the points it was given. And **recovery of lost symbols is
//! proved**: `Model.Polynomial.unisolvence` says the interpolant through enough
//! points on a message polynomial is that polynomial everywhere, including at
//! the nodes whose codewords were destroyed.
//!
//! That last one is the code's central guarantee. The property tests remain, as
//! a check that this transcription computes what the theorem describes rather
//! than as the evidence for the claim itself.

#![forbid(unsafe_code)]
// No `?`: `let`-`else` and `match` instead, for the reason recorded once in
// tacenta-ratchet's module doc ("The `?` operator"). The lint asks for `?`.
#![allow(clippy::question_mark)]

/// The field, mirroring `Model.Gf65536` operation for operation.
///
/// Elements are polynomials over GF(2) of degree below 16, packed into a `u16`
/// with bit `n` the coefficient of `x^n`. Addition is xor. Multiplication is the
/// carry-less product reduced modulo `x^16 + x^12 + x^3 + x + 1`.
pub mod gf {
    /// The reduction polynomial, `0x1100B`. Seventeen bits, so it does not fit
    /// an element; only the low sixteen are ever folded back in.
    pub const REDUCER: u32 = 0x1_100B;

    /// Addition, which in characteristic two is also subtraction.
    #[inline]
    pub fn add(a: u16, b: u16) -> u16 {
        a ^ b
    }

    /// The carry-less product: sixteen shifted copies, xored, into thirty-two
    /// bits so nothing is lost. No reduction here.
    fn clmul(a: u16, b: u16) -> u32 {
        let x = a as u32;
        let mut acc: u32 = 0;
        let mut i: u32 = 0;
        while i < 16 {
            if (b >> i) & 1 == 1 {
                acc ^= x << i;
            }
            i += 1;
        }
        acc
    }

    /// Reduce modulo the field polynomial, highest bit first.
    ///
    /// Order matters: folding at a bit changes lower bits, so a pass upward
    /// would revisit what it had already cleared.
    fn reduce(v: u32) -> u16 {
        let mut v = v;
        let mut i: u32 = 31;
        while i >= 16 {
            if (v >> i) & 1 == 1 {
                v ^= REDUCER << (i - 16);
            }
            i -= 1;
        }
        v as u16
    }

    /// Multiplication: multiply, then reduce.
    #[inline]
    pub fn mul(a: u16, b: u16) -> u16 {
        reduce(clmul(a, b))
    }

    /// Exponentiation by squaring.
    ///
    /// The model writes this as a halving recursion and this writes it as a bit
    /// scan. Both compute `a^n` and the standard argument that they agree is not
    /// reproduced here. What the tests below check is the consequence that
    /// matters, that `inv` inverts, which is false for any transcription that
    /// drifted.
    pub fn pow(a: u16, n: u32) -> u16 {
        let mut base = a;
        let mut e = n;
        let mut acc: u16 = 1;
        while e > 0 {
            if e & 1 == 1 {
                acc = mul(acc, base);
            }
            base = mul(base, base);
            e >>= 1;
        }
        acc
    }

    /// The multiplicative inverse, by Fermat's little theorem: the nonzero
    /// elements form a group of order `2^16 - 1`, so `a^(2^16 - 2)` inverts `a`.
    ///
    /// Zero is returned unchanged. Every caller here divides by the difference
    /// of two distinct nodes, which is never zero.
    #[inline]
    pub fn inv(a: u16) -> u16 {
        if a == 0 { 0 } else { pow(a, 65534) }
    }
}

/// The chunk size in bytes. The published document leaves this to the
/// implementer and notes that larger chunks heal faster.
pub const CHUNK_BYTES: usize = 32;

/// Field elements per chunk: `w/2`, the document's recommendation.
pub const LANES: usize = CHUNK_BYTES / 2;

/// The largest number of codewords one stream can produce, which is the number
/// of distinct nodes the field has.
pub const MAX_CODEWORDS: usize = 65536;

/// A codeword: where it sits in the stream, and its bytes.
///
/// The index travels with the chunk. It is not secret and it is not
/// authenticated here: the Braid authenticates the reconstructed value, not its
/// pieces, so a decoder must treat an index as a hint about placement and
/// nothing more.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Chunk {
    pub index: u16,
    pub data: [u8; CHUNK_BYTES],
}

/// How many chunks a message of this length occupies.
///
/// Public so the Braid can check that a coder restored from persistence is
/// sized for the value its state says it carries (CR-14, CR-21).
pub fn chunk_count(size: usize) -> usize {
    size.div_ceil(CHUNK_BYTES)
}

/// Element `j` of a chunk, big-endian.
fn lane(data: &[u8; CHUNK_BYTES], j: usize) -> u16 {
    let hi = data[2 * j] as u16;
    let lo = data[2 * j + 1] as u16;
    (hi << 8) | lo
}

/// Evaluate, at `x`, the polynomial of degree below `nodes.len()` through the
/// given points.
///
/// `nodes` and `vals` are parallel and must be the same length; a shorter
/// `vals` simply contributes fewer terms, which cannot happen from inside this
/// crate and would not panic if it did.
///
/// The model skips a node by value and this skips by position. They agree when
/// the nodes are distinct, which the decoder guarantees by rejecting a repeated
/// index before a codeword ever reaches here.
///
/// Public so the conformance vectors generated from `Model.Polynomial` can be
/// checked against it. A derivation that cannot be observed cannot be pinned to
/// its model, and this one is specified rather than internal.
pub fn interpolate(nodes: &[u16], vals: &[u16], x: u16) -> u16 {
    let n = nodes.len();
    let mut acc: u16 = 0;
    let mut i = 0;
    while i < n {
        let xi = nodes[i];
        let mut weight: u16 = 1;
        let mut j = 0;
        while j < n {
            if j != i {
                let xj = nodes[j];
                weight = gf::mul(weight, gf::mul(gf::add(x, xj), gf::inv(gf::add(xi, xj))));
            }
            j += 1;
        }
        // An explicit bounds check rather than `vals.get(i)`. The two are the
        // same behaviour, and this one translates into a guarded index that the
        // panic-freedom proof can step through, where `get` reaches the proof
        // as an opaque library call with no specification. Same lesson as the
        // ratchet's: write the code in the form the proofs can use.
        if i < vals.len() {
            acc = gf::add(acc, gf::mul(vals[i], weight));
        }
        i += 1;
    }
    acc
}

/// Barycentric weights for a node set: `w_i = inv(prod_{j != i} (x_i + x_j))`.
///
/// `interpolate` above is the specification, and it recomputes
/// `inv(x_i + x_j)` -- a Fermat exponentiation, some thirty field multiplies
/// -- inside its inner loop, for every lane and every target: `k^2`
/// inversions per lane per reconstructed chunk, tens of milliseconds for the
/// braid's 48-chunk vectors, which is work a chunk nobody has authenticated
/// yet could induce. The weights depend only on the nodes, so they are
/// computed once per node set here -- `k` multiplies and one inversion per
/// node -- and the
/// three functions below reproduce `interpolate` exactly:
///
/// `interpolate(nodes, vals, x) == evaluate(&coefficients(nodes, &weights(nodes), x), vals)`
///
/// for every input, duplicate nodes included (`inv(0) = 0` on both sides, and
/// a product is zero exactly when a factor is). `interpolate` stays as the
/// oracle the conformance vectors and the refinement proof are written
/// against; `interpolate_agrees_with_the_barycentric_form` pins the equality
/// on random inputs until it is a theorem.
pub fn weights(nodes: &[u16]) -> Vec<u16> {
    let n = nodes.len();
    let mut w = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let xi = nodes[i];
        let mut denom: u16 = 1;
        let mut j = 0;
        while j < n {
            if j != i {
                denom = gf::mul(denom, gf::add(xi, nodes[j]));
            }
            j += 1;
        }
        w.push(gf::inv(denom));
        i += 1;
    }
    w
}

/// The Lagrange coefficients at `x`: `c_i = w_i * prod_{j != i} (x + x_j)`.
/// No inversions: those are all in `weights`.
pub fn coefficients(nodes: &[u16], weights: &[u16], x: u16) -> Vec<u16> {
    let n = nodes.len();
    let mut c = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let mut num: u16 = 1;
        let mut j = 0;
        while j < n {
            if j != i {
                num = gf::mul(num, gf::add(x, nodes[j]));
            }
            j += 1;
        }
        let wi = if i < weights.len() { weights[i] } else { 0 };
        c.push(gf::mul(wi, num));
        i += 1;
    }
    c
}

/// `sum_i c_i * vals_i`, over as many terms as both slices carry.
pub fn evaluate(coeffs: &[u16], vals: &[u16]) -> u16 {
    let mut acc: u16 = 0;
    let mut i = 0;
    while i < coeffs.len() {
        if i < vals.len() {
            acc = gf::add(acc, gf::mul(coeffs[i], vals[i]));
        }
        i += 1;
    }
    acc
}

/// A stream of codewords for one message.
#[derive(Clone, PartialEq, Debug)]
pub struct Encoder {
    chunks: Vec<[u8; CHUNK_BYTES]>,
    next: u16,
    exhausted: bool,
}

impl Encoder {
    /// Start a stream. The message is padded with zeros to a chunk boundary; its
    /// true length travels separately, and the decoder is told it up front.
    ///
    /// A message longer than the field can carry -- `MAX_CODEWORDS` chunks,
    /// two megabytes -- is truncated to that many chunks rather than refused.
    /// The cap keeps `next_chunk`'s node index, `s as u16`, from wrapping
    /// and colliding nodes, which would make every parity codeword silently
    /// wrong; it is not reachable through this workspace, whose largest value
    /// is 48 chunks, and an infallible `new` keeps the Braid's send path the
    /// shape its refinement proof is written against (CR-14).
    ///
    /// The cap is a stall at the far end, not a silent loss: the decoder is
    /// told the message's true length, and a length past `MAX_CODEWORDS`
    /// chunks names more codewords than this stream will ever issue, so that
    /// decoder never completes. At the cap the systematic prefix alone spends
    /// every node in the field, so no parity codeword is issued either, and a
    /// receiver that missed one chunk of a capped stream is short for good.
    /// Both are the honest outcome for a message the field cannot carry.
    pub fn new(message: &[u8]) -> Encoder {
        let mut k = chunk_count(message.len());
        if k > MAX_CODEWORDS {
            k = MAX_CODEWORDS;
        }
        let mut chunks = Vec::with_capacity(k);
        let mut t = 0;
        while t < k {
            let mut buf = [0u8; CHUNK_BYTES];
            let start = t * CHUNK_BYTES;
            let mut b = 0;
            while b < CHUNK_BYTES {
                if start + b < message.len() {
                    buf[b] = message[start + b];
                }
                b += 1;
            }
            chunks.push(buf);
            t += 1;
        }
        Encoder {
            chunks,
            next: 0,
            exhausted: false,
        }
    }

    /// How many codewords a decoder needs.
    pub fn needed(&self) -> usize {
        self.chunks.len()
    }

    /// What `new` and `next_chunk` maintain, stated once so `from_bytes` can
    /// check it last and a test can check it after every step. The stream
    /// holds at most `MAX_CODEWORDS` chunks: `new` caps it there and nothing
    /// adds one afterwards, and it is the count that sizes `weights`,
    /// quadratic in it, so a stored stream declaring tens of thousands of
    /// chunks would turn the first non-systematic send into minutes of field
    /// arithmetic (CR-14). And `next_chunk` sets `exhausted` only at the last
    /// index and leaves `next` there, so an exhausted stream at any other
    /// index is a second spelling of no reachable state. `next` itself
    /// carries no bound: it runs past the chunk count as soon as the
    /// systematic prefix has been issued.
    pub fn invariant(&self) -> bool {
        self.chunks.len() <= MAX_CODEWORDS && (!self.exhausted || self.next == u16::MAX)
    }

    /// The next codeword, or `None` once the field's nodes are used up.
    ///
    /// Exhaustion is unreachable in practice: the largest value the Braid sends
    /// is 1536 bytes, or 48 codewords, against 65536 available. It returns
    /// `None` rather than repeating a codeword because a repeat would look to
    /// the decoder like a duplicate and stall the stream with no signal, which
    /// is a worse failure than an obvious one.
    pub fn next_chunk(&mut self) -> Option<Chunk> {
        if self.exhausted {
            return None;
        }
        let index = self.next;
        let t = index as usize;
        let data = if t < self.chunks.len() {
            // Systematic: the first `k` codewords are the message itself.
            self.chunks[t]
        } else {
            let k = self.chunks.len();
            let mut nodes = Vec::with_capacity(k);
            let mut s = 0;
            while s < k {
                nodes.push(s as u16);
                s += 1;
            }
            // Weights once per node set and coefficients once per codeword,
            // shared by all sixteen lanes; see `weights`.
            let w = weights(&nodes);
            let c = coefficients(&nodes, &w, index);
            let mut out = [0u8; CHUNK_BYTES];
            let mut j = 0;
            while j < LANES {
                let mut vals = Vec::with_capacity(k);
                let mut s = 0;
                while s < k {
                    if s < self.chunks.len() {
                        vals.push(lane(&self.chunks[s], j));
                    }
                    s += 1;
                }
                let v = evaluate(&c, &vals);
                out[2 * j] = (v >> 8) as u8;
                out[2 * j + 1] = v as u8;
                j += 1;
            }
            out
        };
        if index == u16::MAX {
            self.exhausted = true;
        } else {
            self.next = index + 1;
        }
        Some(Chunk { index, data })
    }

    /// This stream's state as bytes, for persistence as part of the Braid
    /// that owns it. Not a message on the wire, and not secret -- codewords
    /// of a not-yet-complete message, nothing an attacker learns anything
    /// useful from -- so no `Zeroizing` here; the Braid's own `to_bytes`
    /// wraps the whole composed buffer once, at the top.
    pub fn to_bytes(&self) -> Vec<u8> {
        let len = self.encoded_len();
        let mut out = Vec::with_capacity(len);
        out.extend_from_slice(&self.next.to_be_bytes());
        out.push(if self.exhausted { 0x01 } else { 0x00 });
        out.extend_from_slice(&(self.chunks.len() as u32).to_be_bytes());
        let mut i = 0;
        while i < self.chunks.len() {
            out.extend_from_slice(&self.chunks[i]);
            i += 1;
        }
        // The buffer is sized once, ahead of the first write, so it never
        // grows and never hands a half-written copy of itself back to the
        // allocator. The assertion is what keeps the formula and the writes
        // from drifting apart when either changes.
        debug_assert_eq!(out.len(), len);
        out
    }

    /// Exactly how many bytes `to_bytes` writes: `next`, the exhausted flag
    /// and the chunk count, then every chunk at full width. The same
    /// arithmetic `from_bytes` reads back.
    ///
    /// Public because the Braid embeds this stream in its own persisted
    /// state and sizes that buffer before writing any of it.
    pub fn encoded_len(&self) -> usize {
        2 + 1 + 4 + self.chunks.len() * CHUNK_BYTES
    }

    /// Reconstruct a stream from bytes produced by `to_bytes`.
    pub fn from_bytes(bytes: &[u8]) -> Option<Encoder> {
        if bytes.len() < 2 + 1 + 4 {
            return None;
        }
        let mut next_bytes = [0u8; 2];
        next_bytes.copy_from_slice(&bytes[0..2]);
        let next = u16::from_be_bytes(next_bytes);
        let exhausted = match bytes[2] {
            0x00 => false,
            0x01 => true,
            _ => return None,
        };
        let mut count_bytes = [0u8; 4];
        count_bytes.copy_from_slice(&bytes[3..7]);
        let count = u32::from_be_bytes(count_bytes) as usize;

        // **The count is bounded against the buffer before the loop runs.**
        // Without this the loop below is attacker-controlled and unbounded: a
        // seven-byte header can declare four billion chunks, and since the
        // loop has no early exit (see the note under it) every one of those
        // iterations runs, checks, fails, and continues. An eight-byte input
        // would hang the decoder. `fuzz/fuzz_targets/persisted_state.rs`
        // exercises this shape.
        //
        // The bound rejects nothing the exact check would accept: the `pos !=
        // bytes.len()` check at the end already requires the count to account
        // for the buffer exactly, so a count larger than the buffer could hold
        // fails either way. The difference is that it fails at once rather
        // than after four billion iterations.
        //
        // The bound divides the *whole* buffer rather than what remains after
        // `pos`, deliberately. It is the looser of the two bounds and still
        // more than tight enough -- the exact check at the end does the real
        // work -- and it avoids `bytes.len() - pos`, which would be a
        // subtraction this crate would then have to prove cannot underflow.
        // A new panic site inside a T1-proved function is a worse trade than
        // a bound that admits a few impossible counts a moment longer.
        let mut pos = 7;
        if count > bytes.len() / CHUNK_BYTES {
            return None;
        }
        let mut chunks = Vec::new();
        let mut ok = true;
        for _ in 0..count {
            if bytes.len() < pos + CHUNK_BYTES {
                ok = false;
            } else {
                let mut c = [0u8; CHUNK_BYTES];
                c.copy_from_slice(&bytes[pos..pos + CHUNK_BYTES]);
                chunks.push(c);
                pos += CHUNK_BYTES;
            }
        }
        if !ok || pos != bytes.len() {
            return None;
        }
        // **The restored stream must satisfy what `new` and `next_chunk`
        // maintain**, which is `invariant` in full: the chunk cap `new`
        // imposes, which `Decoder::from_bytes` places on `needed` the same
        // way so the two restore paths stay consistent (CR-14), and
        // exhaustion only at the last index. Checked last, as one predicate,
        // so what the decoder accepts and what the operations keep are the
        // same statement.
        let enc = Encoder {
            chunks,
            next,
            exhausted,
        };
        if !enc.invariant() {
            return None;
        }
        Some(enc)
    }
}

/// Collects codewords until it has enough.
#[derive(Clone, PartialEq, Debug)]
pub struct Decoder {
    size: usize,
    needed: usize,
    have: Vec<Chunk>,
}

impl Decoder {
    /// A decoder for a message of `size` bytes. The size is known in advance
    /// here: this is an erasure code, not a fountain code.
    pub fn new(size: usize) -> Decoder {
        Decoder {
            size,
            needed: chunk_count(size),
            have: Vec::new(),
        }
    }

    /// Offer a codeword. Returns whether it advanced the decoder.
    ///
    /// A repeated index is rejected. That is what keeps the nodes distinct,
    /// which is the hypothesis interpolation needs, and it is also the only
    /// thing standing between a decoder and an adversary who replays one
    /// codeword until the count is satisfied.
    pub fn add_chunk(&mut self, chunk: Chunk) -> bool {
        if self.have.len() >= self.needed {
            return false;
        }
        let mut i = 0;
        while i < self.have.len() {
            if self.have[i].index == chunk.index {
                return false;
            }
            i += 1;
        }
        self.have.push(chunk);
        true
    }

    pub fn has_message(&self) -> bool {
        self.have.len() >= self.needed
    }

    pub fn received(&self) -> usize {
        self.have.len()
    }

    pub fn needed(&self) -> usize {
        self.needed
    }

    /// The length of the message this decoder was told to expect. The Braid
    /// checks it against the length its state implies when it restores a
    /// decoder from persistence (CR-21).
    pub fn size(&self) -> usize {
        self.size
    }

    /// What `new` and `add_chunk` maintain, stated once so `from_bytes` can
    /// check it last and a test can check it after every step. `needed` is
    /// `chunk_count(size)` by construction and at most `MAX_CODEWORDS`, which
    /// bounds `size` by two megabytes and with it what `message()`'s
    /// reservation can cost; `have` never exceeds `needed` and never holds an
    /// index twice, which is the distinct-nodes hypothesis interpolation
    /// needs (`inv(0) = 0` in the field, so a duplicate node would not panic
    /// there; it would reconstruct the wrong bytes without any signal, which
    /// is worse).
    ///
    /// The index pass uses a **bitset** over every possible `u16`, one bit
    /// per index rather than one byte. That keeps the pass linear rather than
    /// quadratic in a count a stored file chooses -- a pairwise scan would be
    /// cheaper for the dozen indices an honest decoder holds, but `have` is
    /// bounded only by `MAX_CODEWORDS`, and 65,536 squared is a slow unit,
    /// not a refusal. It also keeps the frame at 8 KiB rather than the 64 KiB
    /// a `[bool; MAX_CODEWORDS]` costs, which is what this pays per call: the
    /// fuzz targets check the predicate after every step, and the Braid's own
    /// invariant reaches two decoders. A flag rather than a return inside the
    /// loop, which Aeneas does not translate; the loop runs to the end either
    /// way.
    pub fn invariant(&self) -> bool {
        let mut seen = [0u8; MAX_CODEWORDS / 8];
        let mut distinct = true;
        let mut i = 0;
        while i < self.have.len() {
            let idx = self.have[i].index as usize;
            // `idx` is a `u16` widened, so `idx / 8` is in range by
            // construction and the shift is by less than eight.
            let word = idx / 8;
            let bit = 1u8 << (idx % 8);
            if seen[word] & bit != 0 {
                distinct = false;
            }
            seen[word] |= bit;
            i += 1;
        }
        self.needed == chunk_count(self.size)
            && self.needed <= MAX_CODEWORDS
            && self.have.len() <= self.needed
            && distinct
    }

    /// The message, once enough codewords have arrived.
    pub fn message(&self) -> Option<Vec<u8>> {
        if !self.has_message() {
            return None;
        }
        let k = self.needed;
        let mut nodes = Vec::with_capacity(k);
        let mut i = 0;
        while i < k {
            if i < self.have.len() {
                nodes.push(self.have[i].index);
            }
            i += 1;
        }

        // Reserved at the message length rather than at `k * CHUNK_BYTES`.
        // The two differ only by the padding this truncates away at the end, so
        // it is the better hint of the two, and it cannot overflow. The product
        // can: `Decoder::new(usize::MAX)` gives a chunk count whose product with
        // the chunk size is 2^64 exactly. Reaching it would need 2^59 stored
        // codewords, so it is unreachable in practice, but the panic-freedom
        // proof has to discharge the multiplication and cannot; the
        // message-length hint has no such obligation.
        let mut out: Vec<u8> = Vec::with_capacity(self.size);
        // Once per node set, shared by every reconstructed chunk and every
        // lane; see `weights`.
        let w = weights(&nodes);
        let mut t = 0;
        while t < k {
            let target = t as u16;
            let mut direct: Option<&Chunk> = None;
            let mut i = 0;
            while i < k {
                if i < self.have.len() && self.have[i].index == target {
                    direct = Some(&self.have[i]);
                }
                i += 1;
            }
            match direct {
                // Systematic: this chunk arrived as itself.
                Some(c) => out.extend_from_slice(&c.data),
                None => {
                    let c = coefficients(&nodes, &w, target);
                    let mut j = 0;
                    while j < LANES {
                        let mut vals = Vec::with_capacity(k);
                        let mut i = 0;
                        while i < k {
                            if i < self.have.len() {
                                vals.push(lane(&self.have[i].data, j));
                            }
                            i += 1;
                        }
                        let v = evaluate(&c, &vals);
                        out.push((v >> 8) as u8);
                        out.push(v as u8);
                        j += 1;
                    }
                }
            }
            t += 1;
        }
        out.truncate(self.size);
        Some(out)
    }

    /// This decoder's state as bytes, for persistence as part of the Braid
    /// that owns it. `size`/`needed` travel as `u64` rather than the
    /// platform's `usize`, so a state persisted on one width restores
    /// correctly on the other.
    pub fn to_bytes(&self) -> Vec<u8> {
        let len = self.encoded_len();
        let mut out = Vec::with_capacity(len);
        out.extend_from_slice(&(self.size as u64).to_be_bytes());
        out.extend_from_slice(&(self.needed as u64).to_be_bytes());
        out.extend_from_slice(&(self.have.len() as u32).to_be_bytes());
        let mut i = 0;
        while i < self.have.len() {
            let c = &self.have[i];
            out.extend_from_slice(&c.index.to_be_bytes());
            out.extend_from_slice(&c.data);
            i += 1;
        }
        // Sized once, ahead of the first write, for the reason
        // `Encoder::to_bytes` gives; the assertion holds the formula to what
        // the writes actually produce.
        debug_assert_eq!(out.len(), len);
        out
    }

    /// Exactly how many bytes `to_bytes` writes: `size`, `needed` and the
    /// count of codewords held, then each codeword as its index and its
    /// chunk. The same arithmetic `from_bytes` reads back.
    ///
    /// Public for the reason `Encoder::encoded_len` is.
    pub fn encoded_len(&self) -> usize {
        8 + 8 + 4 + self.have.len() * (2 + CHUNK_BYTES)
    }

    /// Reconstruct a decoder from bytes produced by `to_bytes`.
    pub fn from_bytes(bytes: &[u8]) -> Option<Decoder> {
        if bytes.len() < 8 + 8 + 4 {
            return None;
        }
        let mut size_bytes = [0u8; 8];
        size_bytes.copy_from_slice(&bytes[0..8]);
        let size = u64::from_be_bytes(size_bytes) as usize;
        let mut needed_bytes = [0u8; 8];
        needed_bytes.copy_from_slice(&bytes[8..16]);
        let needed = u64::from_be_bytes(needed_bytes) as usize;
        let mut count_bytes = [0u8; 4];
        count_bytes.copy_from_slice(&bytes[16..20]);
        let count = u32::from_be_bytes(count_bytes) as usize;

        // Bounded before the loop, for the reason `Encoder::from_bytes`
        // above gives at length: the loop has no early exit, so an unbounded
        // count is a hang rather than a rejection.
        let mut pos = 20;
        if count > bytes.len() / (2 + CHUNK_BYTES) {
            return None;
        }
        let mut have = Vec::new();
        let mut ok = true;
        for _ in 0..count {
            if bytes.len() < pos + 2 + CHUNK_BYTES {
                ok = false;
            } else {
                let mut idx_bytes = [0u8; 2];
                idx_bytes.copy_from_slice(&bytes[pos..pos + 2]);
                let mut data = [0u8; CHUNK_BYTES];
                data.copy_from_slice(&bytes[pos + 2..pos + 2 + CHUNK_BYTES]);
                have.push(Chunk {
                    index: u16::from_be_bytes(idx_bytes),
                    data,
                });
                pos += 2 + CHUNK_BYTES;
            }
        }
        if !ok || pos != bytes.len() {
            return None;
        }

        // **The restored fields must satisfy what `new` and `add_chunk`
        // maintain, or the decoder that comes back is one no honest run could
        // have produced**, which is `invariant` in full. Without it a stored
        // decoder with `needed = 0` and a huge `size` would decode, re-encode
        // to itself so the session's canonicality check passed, and on the
        // next chunk of its type `has_message()` would be vacuously true and
        // `message()` would ask `Vec::with_capacity` for the huge size -- a
        // panic (capacity overflow) or an abort (allocation failure), on
        // every restart, from one flipped bit in a session file. Checked
        // last, as one predicate, so what the decoder accepts and what the
        // operations keep are the same statement.
        let dec = Decoder { size, needed, have };
        if !dec.invariant() {
            return None;
        }
        Some(dec)
    }
}

#[cfg(test)]
mod decode_bounds_tests {
    use super::*;

    /// Eight bytes that declare a count the buffer cannot hold.
    ///
    /// `next = 1`, `exhausted = true`, `count = 0xfc270000` -- four billion
    /// chunks declared by a buffer holding none. Without the bound the decode
    /// loop would run once per declared chunk, because it has no early exit
    /// (that shape is deliberate, for the Charon and Aeneas translation) and
    /// each iteration only sets a flag: a denial of service rather than a
    /// crash.
    ///
    /// Pinned by value rather than regenerated, so that whoever changes this
    /// decoder next has the input itself rather than a description of it.
    #[test]
    fn a_count_the_buffer_cannot_hold_is_refused_at_once() {
        let found = [0x00u8, 0x01, 0x01, 0xfc, 0x27, 0x00, 0x00, 0x08];
        assert!(Encoder::from_bytes(&found).is_none());

        // The same shape at the widest a `u32` reaches, for both decoders.
        let mut widest = vec![0u8; 7];
        widest[3..7].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(Encoder::from_bytes(&widest).is_none());

        let mut widest_decoder = vec![0u8; 20];
        widest_decoder[16..20].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(Decoder::from_bytes(&widest_decoder).is_none());
    }

    /// A stored encoder declaring one chunk more than the field has nodes is
    /// refused, even when the buffer really holds that many chunks. Two
    /// megabytes of input, once; it is the cheapest form of the restore that
    /// CR-14 describes hanging the first send.
    #[test]
    fn an_encoder_with_more_chunks_than_the_field_has_nodes_is_refused() {
        let count = MAX_CODEWORDS + 1;
        let mut bytes = vec![0u8; 7 + count * CHUNK_BYTES];
        bytes[3..7].copy_from_slice(&(count as u32).to_be_bytes());
        assert!(Encoder::from_bytes(&bytes).is_none());

        // One fewer is the largest stream `new` can build, and it restores.
        let count = MAX_CODEWORDS;
        let mut bytes = vec![0u8; 7 + count * CHUNK_BYTES];
        bytes[3..7].copy_from_slice(&(count as u32).to_be_bytes());
        assert!(Encoder::from_bytes(&bytes).is_some());
    }

    /// `exhausted` is set only when the last index has been issued, and
    /// `next` stays there; a stream claiming exhaustion elsewhere is refused.
    #[test]
    fn an_exhausted_encoder_not_at_the_last_index_is_refused() {
        let msg = vec![1u8; 40];
        let enc = Encoder::new(&msg);
        let mut bytes = enc.to_bytes();
        bytes[2] = 0x01;
        assert!(Encoder::from_bytes(&bytes).is_none());
        bytes[0..2].copy_from_slice(&u16::MAX.to_be_bytes());
        assert!(Encoder::from_bytes(&bytes).is_some());
    }

    /// Each clause of `Decoder::invariant`, violated one at a time in an
    /// otherwise exact encoding, is refused: `needed` off from
    /// `chunk_count(size)`, `needed` past the field's node count, more
    /// codewords held than needed, and one index held twice.
    #[test]
    fn a_decoder_that_breaks_its_own_invariant_is_refused() {
        let msg = vec![7u8; 100];
        let mut enc = Encoder::new(&msg);
        let mut dec = Decoder::new(msg.len());
        dec.add_chunk(enc.next_chunk().unwrap());
        let bytes = dec.to_bytes();
        assert!(Decoder::from_bytes(&bytes).is_some());

        // `needed` is the second `u64`; `size` the first.
        let mut wrong_needed = bytes.clone();
        wrong_needed[8..16].copy_from_slice(&(dec.needed() as u64 + 1).to_be_bytes());
        assert!(Decoder::from_bytes(&wrong_needed).is_none());

        // A size and count that agree with each other but not with the field.
        let mut too_many = Decoder::new((MAX_CODEWORDS + 1) * CHUNK_BYTES).to_bytes();
        assert!(Decoder::from_bytes(&too_many).is_none());
        too_many[0..8].copy_from_slice(&((MAX_CODEWORDS * CHUNK_BYTES) as u64).to_be_bytes());
        too_many[8..16].copy_from_slice(&(MAX_CODEWORDS as u64).to_be_bytes());
        assert!(Decoder::from_bytes(&too_many).is_some());

        // A full decoder plus one: the count is the `u32` after the sizes,
        // and the extra codeword carries an index no other holds.
        let mut full = Decoder::new(msg.len());
        while !full.has_message() {
            full.add_chunk(enc.next_chunk().unwrap());
        }
        let mut over = full.to_bytes();
        over[16..20].copy_from_slice(&(full.received() as u32 + 1).to_be_bytes());
        over.extend_from_slice(&u16::MAX.to_be_bytes());
        over.extend_from_slice(&[0u8; CHUNK_BYTES]);
        assert!(Decoder::from_bytes(&over).is_none());

        // Two codewords at one index, in a decoder with room for both.
        let mut twice = bytes.clone();
        twice[16..20].copy_from_slice(&2u32.to_be_bytes());
        twice.extend_from_slice(&bytes[20..]);
        assert!(Decoder::from_bytes(&twice).is_none());
        // At distinct indices the same two codewords restore.
        let at = 20 + 2 + CHUNK_BYTES;
        twice[at..at + 2].copy_from_slice(&9u16.to_be_bytes());
        assert!(Decoder::from_bytes(&twice).is_some());
    }

    /// Both coders' invariants hold after every step of a lossy stream and
    /// survive a round trip through their persistence at every step, so what
    /// `from_bytes` checks is an inductive invariant of the operations and
    /// not only a shape of the encoding.
    #[test]
    fn the_invariants_hold_after_every_step_and_round_trip() {
        let mut state: u64 = 0x2545_f491_4f6c_dd1d;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut round = 0;
        while round < 6 {
            let len = 1 + (next() % 1600) as usize;
            let mut msg = vec![0u8; len];
            let mut b = 0;
            while b < len {
                msg[b] = next() as u8;
                b += 1;
            }
            let mut enc = Encoder::new(&msg);
            let mut dec = Decoder::new(len);
            assert!(enc.invariant() && dec.invariant());
            let mut steps = 0;
            while !dec.has_message() && steps < 400 {
                let chunk = enc.next_chunk().unwrap();
                assert!(enc.invariant(), "encoder after codeword {steps}");
                // Two in five lost, and one in five offered twice.
                let r = next() % 5;
                if r >= 2 {
                    dec.add_chunk(chunk);
                    assert!(dec.invariant(), "decoder after codeword {steps}");
                }
                if r == 4 {
                    dec.add_chunk(chunk);
                    assert!(dec.invariant(), "decoder after a replay at {steps}");
                }
                enc = Encoder::from_bytes(&enc.to_bytes()).unwrap();
                dec = Decoder::from_bytes(&dec.to_bytes()).unwrap();
                assert!(
                    enc.invariant() && dec.invariant(),
                    "after the round trip at {steps}"
                );
                steps += 1;
            }
            assert_eq!(dec.message().unwrap(), msg, "round {round}");
            round += 1;
        }
    }

    /// `new` caps a stream at the field's node count rather than letting the
    /// node index wrap. At the cap the systematic prefix alone spends every
    /// node: the stream issues exactly `MAX_CODEWORDS` codewords, in order,
    /// the last of them carrying the last chunk kept, and then reports
    /// exhaustion with no parity codeword ever issued. The chunks past the
    /// cap never appear.
    #[test]
    fn new_caps_a_message_at_the_field_size() {
        let mut msg = vec![0x5au8; (MAX_CODEWORDS + 3) * CHUNK_BYTES];
        // Mark the last chunk kept and the first one dropped, so the test can
        // tell which of them the last codeword carries.
        msg[(MAX_CODEWORDS - 1) * CHUNK_BYTES] = 0x01;
        msg[MAX_CODEWORDS * CHUNK_BYTES] = 0x02;
        let mut enc = Encoder::new(&msg);
        assert_eq!(enc.needed(), MAX_CODEWORDS);

        let mut issued = 0usize;
        let mut last = None;
        while let Some(chunk) = enc.next_chunk() {
            assert_eq!(
                chunk.index as usize, issued,
                "codewords are issued in order"
            );
            issued += 1;
            last = Some(chunk);
        }
        assert_eq!(
            issued, MAX_CODEWORDS,
            "one codeword per node, and no parity"
        );
        let last = last.unwrap();
        assert_eq!(last.index, u16::MAX);
        assert_eq!(
            last.data[0], 0x01,
            "the last codeword is the last chunk kept"
        );
        assert!(enc.next_chunk().is_none(), "exhaustion holds");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `interpolate` is the specification; `weights`/`coefficients`/`evaluate`
    /// are the fast form the encoder and decoder now use. They must agree on
    /// every input, duplicate and repeated nodes included, which is what the
    /// refinement theorem will say and this checks on a few thousand random
    /// cases until then.
    #[test]
    fn interpolate_agrees_with_the_barycentric_form() {
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..4000 {
            let n = (next() % 9) as usize;
            let mut nodes = Vec::with_capacity(n);
            let mut vals = Vec::with_capacity(n);
            for _ in 0..n {
                // Small node values so duplicates and `x == x_i` happen often.
                nodes.push((next() % 12) as u16);
                vals.push(next() as u16);
            }
            let x = (next() % 12) as u16;
            let w = weights(&nodes);
            let c = coefficients(&nodes, &w, x);
            assert_eq!(
                interpolate(&nodes, &vals, x),
                evaluate(&c, &vals),
                "nodes {nodes:?} vals {vals:?} x {x}"
            );
        }
    }

    #[test]
    fn field_laws_on_a_sample() {
        // The exhaustive versions are proved in Model/Gf65536.lean. These are
        // here to catch a Rust transcription that drifted from the model.
        for a in [0u16, 1, 2, 0x8000, 0x1234, 0xffff] {
            for b in [0u16, 1, 3, 0x8000, 0x4321, 0xffff] {
                assert_eq!(gf::mul(a, b), gf::mul(b, a));
                assert_eq!(gf::mul(a, 0), 0);
                assert_eq!(gf::mul(a, 1), a);
                for c in [1u16, 7, 0x9999] {
                    assert_eq!(gf::mul(gf::mul(a, b), c), gf::mul(a, gf::mul(b, c)));
                    assert_eq!(
                        gf::mul(a, gf::add(b, c)),
                        gf::add(gf::mul(a, b), gf::mul(a, c))
                    );
                }
                if a != 0 {
                    assert_eq!(gf::mul(a, gf::inv(a)), 1);
                }
            }
        }
    }

    #[test]
    fn in_order_delivery_is_the_message() {
        let msg: Vec<u8> = (0u8..=200).collect();
        let mut enc = Encoder::new(&msg);
        let mut dec = Decoder::new(msg.len());
        while !dec.has_message() {
            dec.add_chunk(enc.next_chunk().unwrap());
        }
        assert_eq!(dec.message().unwrap(), msg);
    }

    #[test]
    fn every_codeword_lost_but_the_last_k() {
        let msg: Vec<u8> = (0u8..=250).collect();
        let mut enc = Encoder::new(&msg);
        let k = enc.needed();
        // Throw away the entire systematic prefix, so nothing arrives directly
        // and every chunk has to be interpolated.
        let mut i = 0;
        while i < k {
            enc.next_chunk().unwrap();
            i += 1;
        }
        let mut dec = Decoder::new(msg.len());
        while !dec.has_message() {
            dec.add_chunk(enc.next_chunk().unwrap());
        }
        assert_eq!(dec.message().unwrap(), msg);
    }

    #[test]
    fn a_replayed_codeword_does_not_advance_the_decoder() {
        let msg = vec![7u8; 100];
        let mut enc = Encoder::new(&msg);
        let mut dec = Decoder::new(msg.len());
        let c = enc.next_chunk().unwrap();
        assert!(dec.add_chunk(c));
        assert!(!dec.add_chunk(c));
        assert!(!dec.add_chunk(c));
        assert_eq!(dec.received(), 1);
        assert!(!dec.has_message());
    }

    /// An `Encoder` mid-stream, with some interpolated codewords already
    /// issued, round-trips byte for byte and keeps issuing the same
    /// subsequent codewords the un-restored original would.
    #[test]
    fn encoder_to_bytes_from_bytes_round_trips() {
        let msg: Vec<u8> = (0u8..=250).collect();
        let mut enc = Encoder::new(&msg);
        // Past the systematic prefix, so at least one issued codeword needed
        // interpolation.
        let mut i = 0;
        while i < enc.needed() + 3 {
            enc.next_chunk().unwrap();
            i += 1;
        }

        let bytes = enc.to_bytes();
        // Sized before the first write and not grown into: the length is
        // exactly what the chunk count implies, which is also what the
        // `debug_assert_eq!` in `to_bytes` checks and what the Braid adds up
        // when it sizes the buffer this stream is embedded in.
        assert_eq!(bytes.len(), 2 + 1 + 4 + enc.needed() * CHUNK_BYTES);
        assert_eq!(bytes.len(), enc.encoded_len());
        let mut restored = Encoder::from_bytes(&bytes).unwrap();
        assert_eq!(enc, restored);

        assert_eq!(restored.next_chunk(), enc.next_chunk());
    }

    #[test]
    fn encoder_from_bytes_rejects_a_truncated_buffer() {
        let msg = vec![9u8; 50];
        let enc = Encoder::new(&msg);
        let bytes = enc.to_bytes();
        assert!(Encoder::from_bytes(&bytes[..bytes.len() - 1]).is_none());
    }

    /// A `Decoder` holding some but not all of the codewords it needs
    /// round-trips byte for byte and keeps working: it still recovers the
    /// message once the rest arrive.
    #[test]
    fn decoder_to_bytes_from_bytes_round_trips() {
        let msg: Vec<u8> = (0u8..=200).collect();
        let mut enc = Encoder::new(&msg);
        let mut dec = Decoder::new(msg.len());
        // Half the needed codewords, so the decoder is genuinely partial.
        let mut i = 0;
        while i < dec.needed() / 2 {
            dec.add_chunk(enc.next_chunk().unwrap());
            i += 1;
        }

        let bytes = dec.to_bytes();
        // Exactly what the codewords held imply, as `Encoder::to_bytes`
        // above.
        assert_eq!(bytes.len(), 8 + 8 + 4 + dec.received() * (2 + CHUNK_BYTES));
        assert_eq!(bytes.len(), dec.encoded_len());
        let mut restored = Decoder::from_bytes(&bytes).unwrap();
        assert_eq!(dec, restored);

        while !restored.has_message() {
            restored.add_chunk(enc.next_chunk().unwrap());
        }
        assert_eq!(restored.message().unwrap(), msg);
    }

    #[test]
    fn decoder_from_bytes_rejects_a_truncated_buffer() {
        let msg = vec![3u8; 60];
        let mut enc = Encoder::new(&msg);
        let mut dec = Decoder::new(msg.len());
        dec.add_chunk(enc.next_chunk().unwrap());
        let bytes = dec.to_bytes();
        assert!(Decoder::from_bytes(&bytes[..bytes.len() - 1]).is_none());
    }

    #[test]
    fn empty_message() {
        let mut dec = Decoder::new(0);
        assert!(dec.has_message());
        assert_eq!(dec.message().unwrap(), Vec::<u8>::new());
        let _ = dec.add_chunk(Chunk {
            index: 0,
            data: [0; CHUNK_BYTES],
        });
    }

    #[test]
    fn a_message_shorter_than_one_chunk() {
        let msg = vec![1u8, 2, 3];
        let mut enc = Encoder::new(&msg);
        let mut dec = Decoder::new(msg.len());
        dec.add_chunk(enc.next_chunk().unwrap());
        assert_eq!(dec.message().unwrap(), msg);
    }

    #[test]
    fn braid_sized_values_survive_arbitrary_loss() {
        // ML-KEM-1024's ek_vector and ct1, the two largest things the Braid
        // sends.
        for size in [1536usize, 1408] {
            let msg: Vec<u8> = (0..size).map(|i| (i * 7 % 251) as u8).collect();
            let mut enc = Encoder::new(&msg);
            let mut dec = Decoder::new(size);
            let mut i = 0usize;
            // Keep one codeword in three.
            while !dec.has_message() {
                let c = enc.next_chunk().unwrap();
                if i.is_multiple_of(3) {
                    dec.add_chunk(c);
                }
                i += 1;
            }
            assert_eq!(dec.message().unwrap(), msg);
        }
    }

    // Unisolvence is proved in Model/Polynomial.lean. These no longer stand in
    // for it: they check that this transcription computes what the theorem
    // describes, over loss patterns a fixed vector set would not reach.
    proptest::proptest! {
        #[test]
        fn any_k_codewords_reconstruct(
            msg in proptest::collection::vec(proptest::prelude::any::<u8>(), 1..400),
            keep in proptest::collection::vec(proptest::prelude::any::<bool>(), 40..200),
        ) {
            let mut enc = Encoder::new(&msg);
            let mut dec = Decoder::new(msg.len());
            let mut i = 0usize;
            while !dec.has_message() {
                let c = enc.next_chunk().unwrap();
                // Drop whatever the pattern says to drop, and take everything
                // once the pattern runs out so the loop always terminates.
                let take = keep.get(i).copied().unwrap_or(true);
                if take {
                    dec.add_chunk(c);
                }
                i += 1;
            }
            proptest::prop_assert_eq!(dec.message().unwrap(), msg);
        }

        #[test]
        fn a_decoder_short_by_one_reconstructs_nothing(
            msg in proptest::collection::vec(proptest::prelude::any::<u8>(), 33..400),
        ) {
            let mut enc = Encoder::new(&msg);
            let k = enc.needed();
            let mut dec = Decoder::new(msg.len());
            let mut n = 0;
            while n + 1 < k {
                dec.add_chunk(enc.next_chunk().unwrap());
                n += 1;
            }
            proptest::prop_assert!(!dec.has_message());
            proptest::prop_assert!(dec.message().is_none());
        }
    }
}
