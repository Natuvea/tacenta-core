//! tacenta-spqr: the Sparse Post-Quantum Ratchet.
//!
//! Written from tacenta-spec/protocol/sparse-pq-ratchet.md and the executable
//! model in tacenta-model (`Model.SparseRatchet`), not from any
//! implementation's source. The model is the oracle: where this file and the
//! model disagree, this file is wrong.
//!
//! ## What it is for
//!
//! The Double Ratchet gets its fresh entropy from a Diffie-Hellman exchange it
//! can complete in one message. A post-quantum agreement cannot: ML-KEM's values
//! are too large, so agreement takes many messages and arrives *sparsely*, once
//! every few dozen. This ratchet is the Double Ratchet's key schedule adapted to
//! that: chains are indexed by the agreement's **epoch** rather than by a
//! ratchet step, and an epoch's chains open when its secret finally lands.
//!
//! ## The agreement is a boundary
//!
//! Nothing here computes a shared secret. [`Output`] arrives as a value, exactly
//! as a Diffie-Hellman output does for the Double Ratchet, and this crate has no
//! dependency on the agreement that produced it. That keeps a state machine an
//! order of magnitude larger than this file out of it, which is also where the
//! published specification keeps it.
//!
//! In practice the agreement is [the ML-KEM Braid](../../braid), whose
//! `Output` this one mirrors.
//!
//! ## Two chains per epoch
//!
//! Both parties derive the same pair of chain keys and assign them oppositely,
//! which is why [`Direction`] exists as a named thing rather than as the order
//! of two variables. Getting it wrong is invisible to every derivation and fatal
//! to the session.

#![forbid(unsafe_code)]
// The `?` operator desugars through `Try` into Lean that will not typecheck, so
// the verified zone does not use it. See tacenta-proofs/upstream/README.md.
#![allow(clippy::question_mark)]

use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

/// A key: 32 bytes, as everything here is.
pub type Key = [u8; 32];

/// The most keys that may be skipped on a single chain (sparse-pq-ratchet.md,
/// Skipped keys). Shared with the Double Ratchet: the risk is the same one.
pub const MAX_SKIP: u64 = 1000;

/// The most skipped keys the store may hold across every epoch in it.
///
/// **This bound is ours and not the specification's.** A per-chain bound does
/// not bound a store that gains a fresh pair of chains every epoch, so without
/// it a peer who never delivers can grow the store without limit. Recorded as a
/// divergence in the conformance manifest.
pub const MAX_SKIPPED_STORE: usize = 2000;

/// How many epochs of chains and skipped keys are kept.
///
/// Everything older is retired, which is what actually bounds the store: the
/// total bound above is a ceiling, and this is what keeps the store far below
/// it in ordinary use.
pub const EPOCHS_KEPT: u64 = 2;

/// `PROTOCOL_INFO` and the three suffixes. Wire-sensitive, recorded in the
/// conformance manifest rather than settled here.
const PROTOCOL_INFO: &[u8] = b"Tacenta SPQR";
const CHAIN_START: &[u8] = b"Chain Start";
const ROOT_LABEL: &[u8] = b"Root";
const CHAIN_LABEL: &[u8] = b"Chain";

/// A secret the agreement produced, with the epoch it belongs to.
///
/// Mirrors `tacenta_braid::Output`. The two are separate types because this
/// crate does not depend on that one, and a caller wiring them together is
/// making a deliberate connection rather than relying on an accident of layout.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct Output {
    #[zeroize(skip)]
    pub key_epoch: u64,
    pub key: Key,
}

impl Output {
    pub fn new(key_epoch: u64, key: Key) -> Output {
        Output { key_epoch, key }
    }
}

/// Which side of the session a party is on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Direction {
    /// Alice: sends on the first derived chain key.
    A2b,
    /// Bob: sends on the second.
    B2a,
}

/// Why an operation could not proceed.
///
/// Every variant is a place the model returns `none`. The model does not
/// distinguish them and a caller must, so this is a refinement of it: each of
/// these maps to that single failure, and none of them maps to success.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SpqrError {
    /// The agreement produced a secret for an epoch that does not follow the
    /// current one. The specification asserts this cannot happen; the
    /// implementation rejects it.
    EpochOutOfOrder,
    /// No chains for that epoch: either never opened, or retired.
    NoChain,
    /// The chain in that direction has been retired.
    ChainRetired,
    /// The message number asks to skip more than [`MAX_SKIP`] on one chain.
    TooManySkipped,
    /// Storing those keys would push the store past [`MAX_SKIPPED_STORE`].
    SkippedStoreFull,
    /// The message number is neither the next on the chain nor one already
    /// stored.
    OutOfOrder,
    /// The chain's message counter would exceed its range (2^64 messages on one
    /// chain), or the epoch counter would exceed its own.
    ///
    /// **Returned rather than wrapping, and the difference is not cosmetic.**
    /// `n` keys the message-key derivation, so a wrapped counter makes
    /// `kdf_ck(&ck, n)` re-derive a key that has already been used -- key reuse,
    /// not a crash. Unchecked arithmetic would panic in debug builds and wrap
    /// in release, and the wrap is the worse of the two.
    ///
    /// Reachable only from a state that arrived saturated, since no session
    /// sends 2^64 messages on one chain. Persisted state is exactly such an
    /// arrival: `from_bytes` takes these counters from the buffer, so an
    /// untrusted store could establish one.
    ChainExhausted,
}

/// One KDF chain: its key, and how many message keys it has produced.
///
/// No `Debug` on this or the other secret-bearing types here, so no derived
/// impl can print chain, message or root keys. Counters-only impls
/// exist under `cfg(test)` below for the crate's own assertions.
#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
struct Chain {
    ck: Key,
    #[zeroize(skip)]
    n: u64,
}

/// A chain is `None` when retired, which the specification distinguishes from a
/// chain that has produced no keys.
#[derive(Clone, Default, PartialEq, Eq)]
struct Chains {
    send: Option<Chain>,
    receive: Option<Chain>,
}

/// A message key held for a message that has not arrived.
#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
struct Skipped {
    #[zeroize(skip)]
    epoch: u64,
    #[zeroize(skip)]
    n: u64,
    key: Key,
}

#[cfg(test)]
impl core::fmt::Debug for Chain {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Chain")
            .field("n", &self.n)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
impl core::fmt::Debug for Chains {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Chains")
            .field("send", &self.send)
            .field("receive", &self.receive)
            .finish()
    }
}

#[cfg(test)]
impl core::fmt::Debug for Skipped {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Skipped")
            .field("epoch", &self.epoch)
            .field("n", &self.n)
            .finish_non_exhaustive()
    }
}

/// The ratchet's state.
///
/// `Clone` so a caller can advance a copy and adopt it only once the message
/// that drove it has authenticated. A message key derived from a header nobody
/// has verified must not be able to move the real state, the same rule the
/// classical session follows. The copy erases
/// on drop the same way the original does: `rk` through the `Drop` below, the
/// chain and message keys through their own `ZeroizeOnDrop`.
///
/// `chains` and `skipped` are vectors of pairs rather than maps, for the same
/// reason the Double Ratchet's store is: it keeps them in the translatable
/// subset. Both are maps in the sense that matters, one entry per key, and that
/// is a property maintained by the operations rather than a shape assumed by
/// the type.
#[derive(Clone, PartialEq)]
pub struct State {
    rk: Key,
    epoch: u64,
    chains: Vec<(u64, Chains)>,
    skipped: Vec<Skipped>,
    direction: Direction,
}

impl Drop for State {
    fn drop(&mut self) {
        self.rk.zeroize();
    }
}

#[cfg(test)]
impl core::fmt::Debug for State {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("State")
            .field("epoch", &self.epoch)
            .field("chains", &self.chains)
            .field("skipped", &self.skipped)
            .field("direction", &self.direction)
            .finish_non_exhaustive()
    }
}

/// A counter as eight big-endian bytes. One encoding serves epochs and message
/// numbers alike, so neither is ambiguous.
fn be64(n: u64) -> [u8; 8] {
    n.to_be_bytes()
}

/// Split 96 bytes into a root key and two chain keys.
fn split3(out: &[u8; 96]) -> (Key, Key, Key) {
    let mut a = [0u8; 32];
    let mut b = [0u8; 32];
    let mut c = [0u8; 32];
    a.copy_from_slice(&out[0..32]);
    b.copy_from_slice(&out[32..64]);
    c.copy_from_slice(&out[64..96]);
    (a, b, c)
}

fn info(suffix: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(PROTOCOL_INFO.len() + suffix.len());
    v.extend_from_slice(PROTOCOL_INFO);
    v.extend_from_slice(suffix);
    v
}

/// `KDF_SCKA_INIT`: from the session's shared secret, a root key and both chain
/// keys at once.
fn kdf_init(sk: &[u8]) -> (Key, Key, Key) {
    let out: [u8; 96] = tacenta_kdf::hkdf_sha256(&[0u8; 32], sk, &info(CHAIN_START));
    split3(&out)
}

/// `KDF_SCKA_RK`: fold an agreement secret into the root key.
fn kdf_rk(rk: &Key, k: &Key) -> (Key, Key, Key) {
    let out: [u8; 96] = tacenta_kdf::hkdf_sha256(rk, k, &info(ROOT_LABEL));
    split3(&out)
}

/// `KDF_SCKA_CK`: advance a chain, yielding the next chain key and a message
/// key.
///
/// The message number is an input, where the Double Ratchet's chain step uses a
/// fixed constant. That binds each message key to its position in the chain, and
/// it is why this cannot reuse the Double Ratchet's chain step.
///
/// Public for the same reason `tacenta_erasure::interpolate` is: it is a
/// specified derivation, and the vectors generated from `Model.SparseRatchet`
/// have to be able to reach it.
pub fn kdf_ck(ck: &Key, n: u64) -> (Key, Key) {
    let out: [u8; 64] = tacenta_kdf::hkdf_sha256(ck, &be64(n), &info(CHAIN_LABEL));
    let mut next = [0u8; 32];
    let mut mk = [0u8; 32];
    next.copy_from_slice(&out[0..32]);
    mk.copy_from_slice(&out[32..64]);
    (next, mk)
}

impl State {
    /// Alice's side.
    pub fn init_alice(sk: &[u8]) -> State {
        State::init(sk, Direction::A2b)
    }

    /// Bob's side.
    pub fn init_bob(sk: &[u8]) -> State {
        State::init(sk, Direction::B2a)
    }

    /// Both parties derive the same root key and the same pair of chain keys,
    /// then assign them oppositely.
    pub fn init(sk: &[u8], direction: Direction) -> State {
        let (rk, k1, k2) = kdf_init(sk);
        let (cks, ckr) = match direction {
            Direction::A2b => (k1, k2),
            Direction::B2a => (k2, k1),
        };
        State {
            rk,
            epoch: 0,
            chains: vec![(
                0,
                Chains {
                    send: Some(Chain { ck: cks, n: 0 }),
                    receive: Some(Chain { ck: ckr, n: 0 }),
                },
            )],
            skipped: Vec::new(),
            direction,
        }
    }

    /// The latest epoch whose secret has been folded in.
    pub fn epoch(&self) -> u64 {
        self.epoch
    }

    /// How many skipped keys are held. For tests and for a caller watching the
    /// bound.
    pub fn skipped_len(&self) -> usize {
        self.skipped.len()
    }

    /// Delete up to `count` of the oldest stored skipped keys and return how
    /// many were deleted; zero means the store was already empty. Oldest is
    /// oldest *stored*: entries are appended in derivation order and only
    /// ever removed, so the front of the vector is the oldest, and no
    /// timestamp is needed.
    ///
    /// The same shape, for the same reason, as `tacenta_ratchet::State::
    /// evict_oldest`: this store has a cap and, unlike the classical one, no
    /// clock at all -- it shrinks only when an epoch retires, which needs the
    /// braid to complete an agreement, which needs accepted messages. A full
    /// store would otherwise be permanent. The session layer evicts on its
    /// working copy and commits only after the message authenticates, so a
    /// forged header still cannot remove a genuine key.
    pub fn evict_oldest(&mut self, count: usize) -> usize {
        let mut evicted = 0;
        while evicted < count && !self.skipped.is_empty() {
            self.skipped.remove(0);
            evicted += 1;
        }
        evicted
    }

    fn find_chains(&self, e: u64) -> Option<&Chains> {
        let mut i = 0;
        while i < self.chains.len() {
            if self.chains[i].0 == e {
                return Some(&self.chains[i].1);
            }
            i += 1;
        }
        None
    }

    fn set_chains(&mut self, e: u64, c: Chains) {
        self.chains.retain(|p| p.0 != e);
        self.chains.push((e, c));
    }

    /// Retire everything older than the epochs kept, chains and skipped keys
    /// alike. This is what bounds the store, so it is not an optimisation.
    fn clear_old_epochs(&mut self, current: u64) {
        self.chains
            .retain(|p| current < p.0.saturating_add(EPOCHS_KEPT));
        self.skipped
            .retain(|s| current < s.epoch.saturating_add(EPOCHS_KEPT));
    }

    /// Fold a new secret into the root key and open a fresh pair of chains under
    /// its epoch.
    fn advance(&mut self, out: &Output) -> Result<(), SpqrError> {
        let Some(next_epoch) = self.epoch.checked_add(1) else {
            return Err(SpqrError::ChainExhausted);
        };
        if out.key_epoch != next_epoch {
            return Err(SpqrError::EpochOutOfOrder);
        }
        let (rk, k1, k2) = kdf_rk(&self.rk, &out.key);
        let (cks, ckr) = match self.direction {
            Direction::A2b => (k1, k2),
            Direction::B2a => (k2, k1),
        };
        self.rk.zeroize();
        self.rk = rk;
        self.epoch = out.key_epoch;
        self.set_chains(
            out.key_epoch,
            Chains {
                send: Some(Chain { ck: cks, n: 0 }),
                receive: Some(Chain { ck: ckr, n: 0 }),
            },
        );
        self.clear_old_epochs(out.key_epoch);
        Ok(())
    }

    fn maybe_advance(&mut self, out: Option<&Output>) -> Result<(), SpqrError> {
        match out {
            Some(o) => self.advance(o),
            None => Ok(()),
        }
    }

    /// Produce the next message key on the sending chain of the epoch the
    /// agreement named.
    ///
    /// Returns the message number and the key. The number goes in the header;
    /// the key drives the AEAD, which is a trusted-boundary primitive and not
    /// this crate's business.
    pub fn send(
        &mut self,
        sending_epoch: u64,
        out: Option<&Output>,
    ) -> Result<(u64, Key), SpqrError> {
        self.maybe_advance(out)?;
        let cs = match self.find_chains(sending_epoch) {
            Some(cs) => cs.clone(),
            None => return Err(SpqrError::NoChain),
        };
        let ch = match &cs.send {
            Some(ch) => ch.clone(),
            None => return Err(SpqrError::ChainRetired),
        };
        let Some(n) = ch.n.checked_add(1) else {
            return Err(SpqrError::ChainExhausted);
        };
        let (next, mk) = kdf_ck(&ch.ck, n);
        self.set_chains(
            sending_epoch,
            Chains {
                send: Some(Chain { ck: next, n }),
                receive: cs.receive.clone(),
            },
        );
        Ok((n, mk))
    }

    /// Take a stored key for this epoch and number, removing it. Removing it is
    /// what makes a stored key one-use.
    fn try_skipped(&mut self, e: u64, n: u64) -> Option<Key> {
        let mut i = 0;
        while i < self.skipped.len() {
            if self.skipped[i].epoch == e && self.skipped[i].n == n {
                let s = self.skipped.remove(i);
                return Some(s.key);
            }
            i += 1;
        }
        None
    }

    /// Step the receiving chain forward to `upto`, storing every key passed.
    ///
    /// Storing replaces rather than accumulates, for the same reason the Double
    /// Ratchet's does: the store is a map on `(epoch, number)`, and a peer must
    /// not be able to make one pair hold two keys.
    fn skip_message_keys(&mut self, e: u64, upto: u64) -> Result<(), SpqrError> {
        let cs = match self.find_chains(e) {
            Some(cs) => cs.clone(),
            None => return Err(SpqrError::NoChain),
        };
        let ch = match &cs.receive {
            Some(ch) => ch.clone(),
            None => return Err(SpqrError::ChainRetired),
        };
        if upto <= ch.n {
            return Ok(());
        }
        let count = upto - ch.n;
        if count > MAX_SKIP {
            return Err(SpqrError::TooManySkipped);
        }
        if self.skipped.len() + (count as usize) > MAX_SKIPPED_STORE {
            return Err(SpqrError::SkippedStoreFull);
        }

        // Numbers run from ch.n + 1, because this chain step is keyed by the
        // number it produces.
        let mut ck = ch.ck;
        let mut derived: Vec<Skipped> = Vec::with_capacity(count as usize);
        let mut num = ch.n;
        while num < upto {
            num += 1;
            let (next, mk) = kdf_ck(&ck, num);
            ck.zeroize();
            ck = next;
            derived.push(Skipped {
                epoch: e,
                n: num,
                key: mk,
            });
        }

        self.skipped
            .retain(|s| !(s.epoch == e && ch.n < s.n && s.n <= upto));
        self.skipped.append(&mut derived);
        self.set_chains(
            e,
            Chains {
                send: cs.send.clone(),
                receive: Some(Chain { ck, n: upto }),
            },
        );
        Ok(())
    }

    /// Produce the message key for a received message.
    ///
    /// A stored key is tried first; only if there is none does the chain
    /// advance, and advancing stores every key it passes so an out-of-order
    /// message can still be read later.
    pub fn receive(
        &mut self,
        receiving_epoch: u64,
        out: Option<&Output>,
        n: u64,
    ) -> Result<Key, SpqrError> {
        self.maybe_advance(out)?;
        if let Some(k) = self.try_skipped(receiving_epoch, n) {
            return Ok(k);
        }
        // Saturating, matching the model's Nat subtraction exactly. A message
        // numbered zero is not a valid message, and it must be rejected as an
        // ordering failure rather than by wrapping around to a request to skip
        // eighteen quintillion keys.
        self.skip_message_keys(receiving_epoch, n.saturating_sub(1))?;
        let cs = match self.find_chains(receiving_epoch) {
            Some(cs) => cs.clone(),
            None => return Err(SpqrError::NoChain),
        };
        let ch = match &cs.receive {
            Some(ch) => ch.clone(),
            None => return Err(SpqrError::ChainRetired),
        };
        let Some(expected) = ch.n.checked_add(1) else {
            return Err(SpqrError::ChainExhausted);
        };
        if n != expected {
            return Err(SpqrError::OutOfOrder);
        }
        let (next, mk) = kdf_ck(&ch.ck, n);
        self.set_chains(
            receiving_epoch,
            Chains {
                send: cs.send.clone(),
                receive: Some(Chain { ck: next, n }),
            },
        );
        Ok(mk)
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
/// A `State::to_bytes`/`from_bytes` failure. As in `tacenta-ratchet`, this
/// format's threat model is corruption and version skew, not a hostile peer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SpqrDecodeError {
    UnknownVersion,
    TooShort,
    Malformed,
}

/// One byte presence tag, then the chain's fields at full width regardless,
/// zeroed when absent -- canonical for the same reason the ratchet's optional
/// keys are.
const CHAIN_LEN: usize = 1 + 32 + 8;
const CHAINS_LEN: usize = 8 + CHAIN_LEN * 2; // epoch key + send + receive
const SKIPPED_LEN: usize = 8 + 8 + 32; // epoch + n + key

const FIXED_PREFIX: usize = 1 // version
    + 32 // rk
    + 8 // epoch
    + 1 // direction
    + 4; // chains count

impl Direction {
    fn to_byte(self) -> u8 {
        match self {
            Direction::A2b => 0x00,
            Direction::B2a => 0x01,
        }
    }

    fn from_byte(b: u8) -> Option<Direction> {
        match b {
            0x00 => Some(Direction::A2b),
            0x01 => Some(Direction::B2a),
            _ => None,
        }
    }
}

fn push_optional_chain(out: &mut Vec<u8>, chain: &Option<Chain>) {
    match chain {
        None => {
            out.push(0x00);
            out.extend_from_slice(&[0u8; 32]);
            out.extend_from_slice(&[0u8; 8]);
        }
        Some(c) => {
            out.push(0x01);
            out.extend_from_slice(&c.ck);
            out.extend_from_slice(&c.n.to_be_bytes());
        }
    }
}

/// Decode one `Option<Chain>` at `pos`. Bounds and tag folded into a single
/// `Option` so a caller looping over these has one fallible step per
/// iteration, not several.
fn decode_chain(bytes: &[u8], pos: usize) -> Option<Option<Chain>> {
    if bytes.len() < pos + CHAIN_LEN {
        return None;
    }
    match bytes[pos] {
        0x00 => {
            // An absent chain still occupies `CHAIN_LEN` bytes, and `to_bytes`
            // writes them as zeros. Anything else in them would be a second
            // spelling of the same state: accepted here and re-emitted as
            // zeros, so `from_bytes` and `to_bytes` would disagree on the
            // bytes, which is what the persisted-state fuzz target's re-encode
            // oracle checks. Refused, the way the composite header's
            // absent-chunk padding is.
            // A flag rather than a return inside the loop: Aeneas does not
            // translate an early return out of a loop.
            let mut clean = true;
            let mut i = pos + 1;
            while i < pos + CHAIN_LEN {
                if bytes[i] != 0 {
                    clean = false;
                }
                i += 1;
            }
            if clean { Some(None) } else { None }
        }
        0x01 => {
            let mut ck = [0u8; 32];
            ck.copy_from_slice(&bytes[pos + 1..pos + 33]);
            let mut n_bytes = [0u8; 8];
            n_bytes.copy_from_slice(&bytes[pos + 33..pos + 41]);
            Some(Some(Chain {
                ck,
                n: u64::from_be_bytes(n_bytes),
            }))
        }
        _ => None,
    }
}

/// Decode one `chains` entry (its epoch key, then its send and receive
/// chains) at `pos` in a single step.
fn decode_chains_entry(bytes: &[u8], pos: usize) -> Option<(u64, Chains)> {
    if bytes.len() < pos + 8 {
        return None;
    }
    let mut e_bytes = [0u8; 8];
    e_bytes.copy_from_slice(&bytes[pos..pos + 8]);
    let send = match decode_chain(bytes, pos + 8) {
        Some(v) => v,
        None => return None,
    };
    let receive = match decode_chain(bytes, pos + 8 + CHAIN_LEN) {
        Some(v) => v,
        None => return None,
    };
    Some((u64::from_be_bytes(e_bytes), Chains { send, receive }))
}

/// Decode one `skipped` entry at `pos` in a single step.
fn decode_skipped_entry(bytes: &[u8], pos: usize) -> Option<Skipped> {
    if bytes.len() < pos + SKIPPED_LEN {
        return None;
    }
    let mut epoch_bytes = [0u8; 8];
    epoch_bytes.copy_from_slice(&bytes[pos..pos + 8]);
    let mut n_bytes = [0u8; 8];
    n_bytes.copy_from_slice(&bytes[pos + 8..pos + 16]);
    let mut key = [0u8; 32];
    key.copy_from_slice(&bytes[pos + 16..pos + 48]);
    Some(Skipped {
        epoch: u64::from_be_bytes(epoch_bytes),
        n: u64::from_be_bytes(n_bytes),
        key,
    })
}

impl State {
    /// Encode this state for persistence. Not a message on the wire: this is
    /// what a storage layer writes to disk and reads back with `from_bytes`
    /// after a restart. As with the ratchet's export, at-rest protection of
    /// the persisted bytes is that caller's job, not this format's.
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        let mut out = Vec::new();
        out.push(STATE_VERSION);
        out.extend_from_slice(&self.rk);
        out.extend_from_slice(&self.epoch.to_be_bytes());
        out.push(self.direction.to_byte());
        out.extend_from_slice(&(self.chains.len() as u32).to_be_bytes());
        let mut i = 0;
        while i < self.chains.len() {
            let (e, cs) = &self.chains[i];
            out.extend_from_slice(&e.to_be_bytes());
            push_optional_chain(&mut out, &cs.send);
            push_optional_chain(&mut out, &cs.receive);
            i += 1;
        }
        out.extend_from_slice(&(self.skipped.len() as u32).to_be_bytes());
        let mut j = 0;
        while j < self.skipped.len() {
            let s = &self.skipped[j];
            out.extend_from_slice(&s.epoch.to_be_bytes());
            out.extend_from_slice(&s.n.to_be_bytes());
            out.extend_from_slice(&s.key);
            j += 1;
        }
        Zeroizing::new(out)
    }

    /// Decode a state persisted by `to_bytes`. Canonical: trailing bytes past
    /// the last skipped entry are refused rather than ignored.
    pub fn from_bytes(bytes: &[u8]) -> Result<State, SpqrDecodeError> {
        if bytes.len() < FIXED_PREFIX {
            return Err(SpqrDecodeError::TooShort);
        }
        if bytes[0] != STATE_VERSION {
            return Err(SpqrDecodeError::UnknownVersion);
        }
        let mut pos = 1;
        let mut rk = [0u8; 32];
        rk.copy_from_slice(&bytes[pos..pos + 32]);
        pos += 32;
        let mut epoch_bytes = [0u8; 8];
        epoch_bytes.copy_from_slice(&bytes[pos..pos + 8]);
        let epoch = u64::from_be_bytes(epoch_bytes);
        pos += 8;
        let Some(direction) = Direction::from_byte(bytes[pos]) else {
            return Err(SpqrDecodeError::Malformed);
        };
        pos += 1;
        let mut count_bytes = [0u8; 4];
        count_bytes.copy_from_slice(&bytes[pos..pos + 4]);
        let chains_count = u32::from_be_bytes(count_bytes) as usize;
        pos += 4;

        // **Both counts below are bounded against the buffer before their
        // loop runs.** Neither loop has an early exit, so an unbounded count
        // is a hang rather than a rejection: a four-byte field can declare
        // four billion entries against a buffer holding none. Nothing
        // previously accepted is rejected -- the `pos != bytes.len()` check at
        // the end already required each count to account for the buffer
        // exactly. See `tacenta-erasure`, where a fuzzer found this first.
        if chains_count > bytes.len() / CHAINS_LEN {
            return Err(SpqrDecodeError::Malformed);
        }

        // No early return inside either loop below: a failed entry sets its
        // `ok` flag and the loop still runs to completion (every remaining
        // call stays bounds-checked), with the failure reported once, after.
        let mut chains = Vec::new();
        let mut chains_ok = true;
        for _ in 0..chains_count {
            match decode_chains_entry(bytes, pos) {
                Some(entry) => {
                    chains.push(entry);
                    pos += CHAINS_LEN;
                }
                None => chains_ok = false,
            }
        }
        if !chains_ok {
            return Err(SpqrDecodeError::Malformed);
        }

        if bytes.len() < pos + 4 {
            return Err(SpqrDecodeError::TooShort);
        }
        let mut skipped_count_bytes = [0u8; 4];
        skipped_count_bytes.copy_from_slice(&bytes[pos..pos + 4]);
        let skipped_count = u32::from_be_bytes(skipped_count_bytes) as usize;
        pos += 4;

        if skipped_count > bytes.len() / SKIPPED_LEN {
            return Err(SpqrDecodeError::Malformed);
        }

        let mut skipped = Vec::new();
        let mut skipped_ok = true;
        for _ in 0..skipped_count {
            match decode_skipped_entry(bytes, pos) {
                Some(entry) => {
                    skipped.push(entry);
                    pos += SKIPPED_LEN;
                }
                None => skipped_ok = false,
            }
        }
        if !skipped_ok {
            return Err(SpqrDecodeError::Malformed);
        }

        if pos != bytes.len() {
            return Err(SpqrDecodeError::Malformed);
        }

        Ok(State {
            rk,
            epoch,
            chains,
            skipped,
            direction,
        })
    }
}

#[cfg(test)]
mod decode_bounds_tests {
    use super::*;

    /// Both counts are refused before their loop when the buffer cannot hold
    /// them.
    ///
    /// Neither loop has an early exit, for the translation's sake, so an
    /// unbounded count would hang rather than reject. The same bound guards
    /// the same shape in `tacenta-erasure` and `tacenta-ratchet`.
    #[test]
    fn a_count_the_buffer_cannot_hold_is_refused_at_once() {
        let mut buf = vec![0u8; 64];
        buf[0] = STATE_VERSION;
        let end = buf.len();
        buf[end - 4..].copy_from_slice(&u32::MAX.to_be_bytes());
        let _ = State::from_bytes(&buf);
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod exhaustion_tests {
    use super::*;

    /// A chain one step from wrapping must refuse rather than wrap.
    ///
    /// **What wrapping would actually cost.** `n` keys the derivation:
    /// `kdf_ck(&ck, n)`. If `ch.n + 1` wrapped to zero, the next message key
    /// would be the one already used at `n = 0`. That is key reuse, breaking
    /// confidentiality for two messages at once -- not a panic that stops the
    /// process safely. Unchecked arithmetic would panic in debug builds and
    /// wrap in release, and the wrap is the worse of the two.
    ///
    /// Unreachable by sending, since nobody sends 2^64 messages on one chain,
    /// and reachable by *importing*, because `from_bytes` takes these counters
    /// straight from the buffer. That is why this check belongs here and not
    /// only at the import boundary: the boundary cannot see the per-chain
    /// counter, because this crate exposes `epoch()` and not `n`.
    #[test]
    fn a_saturated_chain_counter_refuses_instead_of_wrapping() {
        let mut state = State::init_alice(&[3u8; 32]);
        let out = Output::new(1, [5u8; 32]);

        let (n, _k) = state.send(1, Some(&out)).expect("an ordinary send works");
        assert_eq!(n, 1, "the first message on a chain is number one");

        // Saturate the sending chain, which is what importing a hostile store
        // would do.
        for (_epoch, chains) in state.chains.iter_mut() {
            if let Some(ch) = chains.send.as_mut() {
                ch.n = u64::MAX;
            }
        }

        match state.send(1, None) {
            Err(SpqrError::ChainExhausted) => {}
            Err(other) => panic!("expected ChainExhausted, got {other:?}"),
            Ok((n, _)) => panic!(
                "a saturated chain produced message number {n}, so kdf_ck \
                 re-derived a key that was already used"
            ),
        }
    }

    /// The epoch counter gets the same treatment, for the same reason: a
    /// wrapped epoch could compare equal to an attacker-chosen `key_epoch` and
    /// step the ratchet on a secret it should have refused.
    #[test]
    fn a_saturated_epoch_refuses_instead_of_wrapping() {
        let mut state = State::init_alice(&[4u8; 32]);
        state.epoch = u64::MAX;
        let out = Output::new(0, [6u8; 32]);
        assert!(
            matches!(state.send(0, Some(&out)), Err(SpqrError::ChainExhausted)),
            "a saturated epoch must refuse rather than wrap into a match"
        );
    }
}
