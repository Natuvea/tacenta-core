//! tacenta-triple: the Triple Ratchet.
//!
//! Written from tacenta-spec/protocol/triple-ratchet.md, not from any
//! implementation's source.
//!
//! The name counts ratchets rather than steps: the Double Ratchet's two, plus
//! the sparse post-quantum one. What the composition adds is not a third
//! mechanism but a rule for using the two it already has.
//!
//! ## Run both, encrypt with neither
//!
//! Each ratchet is asked only for a message key. The key that actually encrypts
//! is derived from the pair. An attacker must break the elliptic-curve
//! assumptions *and* the post-quantum ones; breaking either alone yields one
//! input and nothing else.
//!
//! This is why the sparse ratchet is not deployed on its own. Replacing the
//! Diffie-Hellman ratchet with a post-quantum one substitutes one assumption for
//! another: better against a future quantum adversary, worse against a classical
//! one, since the post-quantum agreement is younger and heals more slowly.
//! Running both is the only arrangement that keeps every guarantee we have and
//! adds one.
//!
//! It is also what makes the agreement's output safe to use. A Braid epoch key
//! is derived from the KEM shared secret and the epoch alone, with no binding to
//! the handshake or the peers, so it must never be a session key by itself. Here
//! it is combined with a Double Ratchet message key whose whole lineage runs back
//! through the handshake, and that is where the binding comes from.
//!
//! ## The two ratchets do not know about each other
//!
//! Neither state refers to the other. **The Double Ratchet is unchanged**: its
//! derivations, its skipped-key handling, and everything proved about it carry
//! over untouched. Only its output changes role, from the encryption key to one
//! of two inputs to one.
//!
//! That independence does not make partial failure harmless; why not, and how
//! it is prevented, is covered at [`State::send`] and [`State::receive`].

#![forbid(unsafe_code)]
// No `?`: `let`-`else` and `match` instead, for the reason recorded once in
// tacenta-ratchet's module doc ("The `?` operator"). The lint asks for `?`.
#![allow(clippy::question_mark)]

use zeroize::{Zeroize, Zeroizing};

pub use tacenta_ratchet::{Header as DrHeader, Key, LabelSet, RatchetError};
pub use tacenta_spqr::{Output, SpqrError};

/// `PROTOCOL_INFO` for the combination and the split. Wire-sensitive, recorded
/// in the conformance manifest rather than settled here.
/// `TR_PROTOCOL_INFO` in the specification's terms: the protocol and its
/// parameters, in the shape the published examples use.
///
/// §6.3 asks for a constant specifying "the protocol in use **and its
/// parameters**". A value naming only the protocol would let two deployments
/// differing solely in hash derive the same key from the same inputs -- the
/// confusion domain separation exists to prevent.
const COMBINE_INFO: &[u8] = b"Tacenta_CURVE25519_SHA-256_MLKEM1024";
/// The same protocol constant as `COMBINE_INFO`, with a literal suffix.
///
/// That is the published pattern for a derivation the specification does not
/// name its own constant for: §5.2's SCKA functions are `SPQR_PROTOCOL_INFO`
/// joined to "Chain Start" and "Chain Add Epoch".
///
/// §7.1 mandates that the handshake secret is expanded into two and does not
/// give the constant that expands it, so this one is ours. Naming the
/// parameters here is hygiene rather than conformance, and it is the same
/// hygiene: one constant parameterised and its neighbour not would be worse
/// than either choice made consistently.
///
/// `COMBINE_INFO` is a prefix of this, harmlessly. The two derivations take
/// different salts and different keying material, so the constant is not the
/// only thing separating them.
const SPLIT_INFO: &[u8] = b"Tacenta_CURVE25519_SHA-256_MLKEM1024:Split";

/// The composite header: each ratchet's own, side by side.
///
/// The specification requires this to parse unambiguously. That is an
/// obligation on the encoding rather than on the ratchets, and it is discharged
/// on the message-format page. Here the two halves are separate fields, so the
/// question does not arise until something serializes them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Header {
    /// The Diffie-Hellman ratchet's public key, previous chain length, and
    /// message number.
    pub dr: DrHeader,
    /// The agreement epoch this message's post-quantum key comes from.
    pub epoch: u64,
    /// The message number on that epoch's chain.
    pub pq_n: u64,
}

/// Why an operation could not proceed. One variant per contributing ratchet,
/// because a caller responds to them differently and flattening them would
/// throw that away.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TripleError {
    /// The Double Ratchet half refused.
    Classical(RatchetError),
    /// The post-quantum half refused.
    PostQuantum(SpqrError),
}

/// Expand the handshake's single shared secret into one for each ratchet.
///
/// This is the only change the composition forces on the handshake, and it has
/// to be made in the specification, the model, and the implementation together.
/// Each ratchet needs its own thirty-two bytes and the handshake produces one
/// set, so the secret is expanded rather than shared: giving both ratchets the
/// same secret would make the hybrid claim false at initialisation, whatever it
/// looked like afterwards.
pub fn split_secret(sk: &[u8]) -> (Key, Key) {
    // Wiped on the way out: the 64 bytes hold both ratchets' secrets (CR-15).
    let out = Zeroizing::new(tacenta_kdf::hkdf_sha256::<64>(&[0u8; 32], sk, SPLIT_INFO));
    let mut ec = [0u8; 32];
    let mut pq = [0u8; 32];
    ec.copy_from_slice(&out[0..32]);
    pq.copy_from_slice(&out[32..64]);
    (ec, pq)
}

/// Derive the encryption key from the two message keys.
///
/// A derivation over the concatenation, under a constant naming the protocol.
/// The concatenation is unambiguous for free: both inputs are exactly
/// thirty-two bytes, so no two distinct pairs present the same bytes.
pub fn combine(mk_classical: &Key, mk_pq: &Key) -> Key {
    // Salt is the post-quantum key, IKM the classical one, per §7.2 of the
    // published Double Ratchet specification. The inversion is the same one
    // `KDF_RK` has and is easy to get backwards; §6.3's looser definition is
    // a derivation keyed by the concatenation of both.
    //
    // Nothing to zeroize here: no concatenation buffer is built, so no copy of
    // either key outlives the call.
    tacenta_kdf::hkdf_sha256(mk_pq, mk_classical, COMBINE_INFO)
}

/// One party's state: two ratchets, side by side and independent.
///
/// No `Debug`: both halves hold key material, and the leaf crates
/// withhold `Debug` from their states for the same reason. Tests that need
/// to print one compare the halves' counters through the accessors.
///
/// No equality either. Both halves compare only under their own crates'
/// `cfg(test)`, which a dependent's tests do not see, and a derived
/// comparison here would be byte-wise over key material and not
/// constant-time; the round-trip tests compare encodings instead (CR-22).
#[derive(Clone)]
pub struct State {
    classical: tacenta_ratchet::State,
    post_quantum: tacenta_spqr::State,
}

#[cfg(test)]
impl core::fmt::Debug for State {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("State")
            .field("send_count", &self.classical.send_count())
            .field("receive_count", &self.classical.receive_count())
            .field("epoch", &self.post_quantum.epoch())
            .field("pq_skipped", &self.post_quantum.skipped_len())
            .finish_non_exhaustive()
    }
}

impl State {
    /// The party that speaks first.
    ///
    /// Takes the handshake's shared secret and splits it. The remaining
    /// arguments are the Double Ratchet's, unchanged.
    pub fn init_sender(
        sk: &[u8],
        our_pub: Key,
        peer_pub: Key,
        dh_out: &Key,
        labels: LabelSet,
    ) -> State {
        let (mut ec, mut pq) = split_secret(sk);
        let s = State {
            classical: tacenta_ratchet::init_sender(&ec, our_pub, peer_pub, dh_out, labels),
            post_quantum: tacenta_spqr::State::init_alice(&pq),
        };
        ec.zeroize();
        pq.zeroize();
        s
    }

    /// The party that waits.
    pub fn init_receiver(sk: &[u8], our_pub: Key, labels: LabelSet) -> State {
        let (mut ec, mut pq) = split_secret(sk);
        let s = State {
            classical: tacenta_ratchet::init_receiver(&ec, our_pub, labels),
            post_quantum: tacenta_spqr::State::init_bob(&pq),
        };
        ec.zeroize();
        pq.zeroize();
        s
    }

    /// The Diffie-Hellman ratchet's current public key, for the caller that
    /// performs the agreement.
    pub fn sending_public(&self) -> Key {
        self.classical.sending_public()
    }

    /// Messages sent on the classical chain, for the observable state.
    ///
    /// Delegated rather than exposed, so a caller cannot reach past the
    /// composition into one half of it.
    pub fn send_count(&self) -> u32 {
        self.classical.send_count()
    }

    /// Messages received on the classical chain.
    pub fn receive_count(&self) -> u32 {
        self.classical.receive_count()
    }

    /// Skipped message keys the classical ratchet holds, for the caller
    /// sizing an eviction (see `evict_oldest_classical`): the store refuses
    /// when this plus the keys a message skips would pass the cap, so the
    /// room to make is that excess, not the skip count (CR-19).
    pub fn classical_skipped_len(&self) -> usize {
        self.classical.skipped_len()
    }

    /// Make room in the classical ratchet's skipped-key store by deleting up
    /// to `count` of its oldest keys; returns how many were deleted. See
    /// `tacenta_ratchet::State::evict_oldest` for why this exists and why it
    /// must only be called on a copy that is committed after authentication.
    /// `#[must_use]` for the reason given there: zero means the store was
    /// empty, and a caller that does not look will retry forever.
    #[must_use]
    pub fn evict_oldest_classical(&mut self, count: usize) -> usize {
        self.classical.evict_oldest(count)
    }

    /// The post-quantum counterpart of `evict_oldest_classical`.
    #[must_use]
    pub fn evict_oldest_post_quantum(&mut self, count: usize) -> usize {
        self.post_quantum.evict_oldest(count)
    }

    /// The latest agreement epoch folded into the post-quantum half.
    pub fn epoch(&self) -> u64 {
        self.post_quantum.epoch()
    }

    /// Produce a header and the key that encrypts this message.
    ///
    /// `sending_epoch` and `output` come from the agreement beneath: the epoch
    /// both parties are known to hold, and its secret on the message where one
    /// first becomes available.
    ///
    /// ## When one half refuses
    ///
    /// The classical half runs first, so its ordinary transient failure, having
    /// no sending chain before anything has been received, leaves the
    /// post-quantum half untouched.
    ///
    /// **A failed send changes nothing.** The argument for the alternative is
    /// worth recording because it is tempting.
    ///
    /// The classical ratchet runs first, so without the copy a post-quantum
    /// failure would leave a classical message key consumed for a message never
    /// sent. That looks harmless: the number is never on the wire, so the peer
    /// skips it, stores one key it will never spend, and ages it out. The two
    /// ratchets are indexed independently, so neither depends on the other.
    ///
    /// It is the same argument that would excuse partial advancement in this
    /// crate's `receive`, and it fails the same way. It is *smaller* here,
    /// because a send is driven by our own state rather than by bytes a peer
    /// chose, so nobody outside picks the moment. Smaller is not zero: repeated
    /// failures push a peer's skipped-key store up without a single message
    /// arriving, and "harmless" does more work in that sentence than it can
    /// carry.
    ///
    /// So it runs against a copy and assigns on success. The signature stays
    /// `&mut self` rather than becoming a candidate and a `commit` like
    /// `receive`, because there is no authenticator to wait for: the caller has
    /// nothing to decide between deriving and committing.
    pub fn send(
        &mut self,
        sending_epoch: u64,
        output: Option<&Output>,
    ) -> Result<(Header, Key), TripleError> {
        let mut candidate = self.clone();
        let (dr, mut mk_ec) = match tacenta_ratchet::send(&mut candidate.classical) {
            Ok(v) => v,
            Err(e) => return Err(TripleError::Classical(e)),
        };
        let (pq_n, mut mk_pq) = match candidate.post_quantum.send(sending_epoch, output) {
            Ok(v) => v,
            Err(e) => {
                mk_ec.zeroize();
                return Err(TripleError::PostQuantum(e));
            }
        };
        *self = candidate;
        let key = combine(&mk_ec, &mk_pq);
        mk_ec.zeroize();
        mk_pq.zeroize();
        Ok((
            Header {
                dr,
                epoch: sending_epoch,
                pq_n,
            },
            key,
        ))
    }

    /// Recover the key that decrypts a message, **without changing anything**.
    ///
    /// Each half of the header goes to its own ratchet and the two keys are
    /// combined the same way. What comes back is the key and the state this
    /// message *would* produce. Nothing in `self` moves until [`commit`] is
    /// called, and the caller must call it only once the message's own
    /// authenticator has verified.
    ///
    /// [`commit`]: State::commit
    ///
    /// ## Why this does not take `&mut self`
    ///
    /// The argument for advancing in place would be that partial advancement is
    /// harmless: each ratchet is driven by its own half of each header, so a
    /// later message tells both halves what to do regardless. That argument
    /// fails here for the same reason it fails in the classical session.
    /// Advancing on a message that never authenticates consumes the key of one
    /// that would have, and over two state machines rather than one it consumes
    /// more.
    ///
    /// Authentication happens above this layer: this crate derives keys and
    /// never sees a tag. A layer that cannot verify must not be able to commit,
    /// so the only way to advance the state is to be handed a candidate and
    /// choose to adopt it. The unsafe shape is not documented here, it is
    /// unavailable.
    pub fn receive(
        &self,
        header: &Header,
        dh_out_recv: &Key,
        dh_out_send: &Key,
        new_dhs_pub: Key,
        output: Option<&Output>,
    ) -> Result<(State, Key), TripleError> {
        let mut candidate = self.clone();
        let mut mk_ec = match tacenta_ratchet::receive(
            &mut candidate.classical,
            &header.dr,
            dh_out_recv,
            dh_out_send,
            new_dhs_pub,
        ) {
            Ok(v) => v,
            Err(e) => return Err(TripleError::Classical(e)),
        };
        let mut mk_pq = match candidate
            .post_quantum
            .receive(header.epoch, output, header.pq_n)
        {
            Ok(v) => v,
            Err(e) => {
                mk_ec.zeroize();
                return Err(TripleError::PostQuantum(e));
            }
        };
        let key = combine(&mk_ec, &mk_pq);
        mk_ec.zeroize();
        mk_pq.zeroize();
        Ok((candidate, key))
    }

    /// Adopt the state a [`receive`] produced.
    ///
    /// Call this only after the message that produced it has authenticated.
    /// Everything the receive would have changed happens here, at once: both
    /// ratchets, the skipped-key stores, and the epoch.
    ///
    /// [`receive`]: State::receive
    pub fn commit(&mut self, next: State) {
        *self = next;
    }
}

/// This crate's own persistence-format version (`State::to_bytes`/
/// `from_bytes`), separate from any on-the-wire message version: this is what
/// a storage layer writes to disk and reads back after a restart, not
/// anything a peer ever receives.
const STATE_VERSION: u8 = 0x01;

/// Named with the crate's own prefix rather than plainly `DecodeError`, which
/// reads redundantly inside this crate and is deliberate. Charon emits
/// discriminant instances unqualified, so each crate's error enum carries a
/// distinct name. The redundancy in here buys uniqueness out there. Do not
/// tidy it.
///
/// A `State::to_bytes`/`from_bytes` failure. As in the two ratchets this
/// composes, the threat model is corruption and version skew, not a hostile
/// peer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TripleDecodeError {
    UnknownVersion,
    TooShort,
    Malformed,
}

/// Read one length-prefixed field at `pos`, returning it and the position
/// just past it. A plain function, not a loop.
fn take_len_prefixed(bytes: &[u8], pos: usize) -> Option<(&[u8], usize)> {
    // `checked_add` on both sums: the 32-bit wrap the wire decoders' `take_at`
    // guards against, applied here too. Matches rather than `?` to
    // stay in the translatable subset.
    let start = match pos.checked_add(4) {
        Some(s) => s,
        None => return None,
    };
    if bytes.len() < start {
        return None;
    }
    let mut len_bytes = [0u8; 4];
    len_bytes.copy_from_slice(&bytes[pos..start]);
    let len = u32::from_be_bytes(len_bytes) as usize;
    let end = match start.checked_add(len) {
        Some(e) => e,
        None => return None,
    };
    if bytes.len() < end {
        return None;
    }
    Some((&bytes[start..end], end))
}

impl State {
    /// Encode this state for persistence: the version byte, then each ratchet's
    /// own `to_bytes`, length-prefixed. Not a message on the wire -- see the
    /// session layer above for that -- this is what a storage layer writes to
    /// disk and reads back with `from_bytes` after a restart. At-rest
    /// protection of the persisted bytes is that caller's job, the same as for
    /// the two formats this composes.
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        let mut out = Vec::new();
        out.push(STATE_VERSION);
        let classical = self.classical.to_bytes();
        out.extend_from_slice(&(classical.len() as u32).to_be_bytes());
        out.extend_from_slice(&classical);
        let post_quantum = self.post_quantum.to_bytes();
        out.extend_from_slice(&(post_quantum.len() as u32).to_be_bytes());
        out.extend_from_slice(&post_quantum);
        Zeroizing::new(out)
    }

    /// Decode a state persisted by `to_bytes`.
    pub fn from_bytes(bytes: &[u8]) -> Result<State, TripleDecodeError> {
        if bytes.is_empty() {
            return Err(TripleDecodeError::TooShort);
        }
        if bytes[0] != STATE_VERSION {
            return Err(TripleDecodeError::UnknownVersion);
        }
        let Some((classical_bytes, pos)) = take_len_prefixed(bytes, 1) else {
            return Err(TripleDecodeError::TooShort);
        };
        let Ok(classical) = tacenta_ratchet::State::from_bytes(classical_bytes) else {
            return Err(TripleDecodeError::Malformed);
        };
        let Some((pq_bytes, pos)) = take_len_prefixed(bytes, pos) else {
            return Err(TripleDecodeError::TooShort);
        };
        let Ok(post_quantum) = tacenta_spqr::State::from_bytes(pq_bytes) else {
            return Err(TripleDecodeError::Malformed);
        };
        if pos != bytes.len() {
            return Err(TripleDecodeError::Malformed);
        }
        Ok(State {
            classical,
            post_quantum,
        })
    }
}

#[cfg(test)]
mod tests;
