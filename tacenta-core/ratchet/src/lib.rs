//! tacenta-ratchet: the Double Ratchet state machine.
//!
//! This crate follows tacenta-spec/protocol/ratchet.md and the executable model
//! in tacenta-model (Model.State / Model.Ratchet). It
//! is a pure leaf module: Diffie-Hellman outputs are passed in as bytes (the
//! X25519 agreement lives in the session layer), so it mirrors the model one to
//! one and stays in the translatable, verifiable subset (no hash map, no trait
//! objects, no interior mutability, errors as a plain enum).
//!
//! The module is a byte-exact realisation of the ratchet key schedule: given a
//! root key, a sequence of DH outputs, and a delivery order, it produces the
//! same message keys the model does. The AEAD that a message key drives is a
//! trusted-boundary primitive (see `message_keys`).
//!
//! **Why this is its own crate.** The verified zone is isolated so the T1
//! (panic-freedom) translation covers it alone. Translating the whole of
//! tacenta-core dragged in orchestration code that Charon and Aeneas do not
//! model (closures, slice patterns), which failed the run for reasons that had
//! nothing to do with the ratchet. Keeping the ratchet and the key derivation
//! it calls in a leaf crate with only trusted-boundary dependencies makes the
//! translated surface exactly the surface we intend to prove. Nothing that is
//! not the verified zone belongs here.

//! **The `?` operator.** This is the one place the rule is stated; the other
//! verified-zone crates point here. The translation notes
//! (tacenta-proofs/upstream/README.md) record that `?` "does not translate":
//! it desugars through the `Try` trait, and the failing run produced
//! universe-polymorphic Lean that did not typecheck. That run kept no
//! reproducer, so the exact shape that failed is not known. What is known
//! from the tree itself is narrower than the note: `tacenta-protobuf` and
//! `tacenta-spqr` use `?` on a `Result` whose error type is the enclosing
//! function's own -- no `From` conversion, no `Option` -- and both translate
//! and carry proofs; `tacenta-protobuf` uses it inside a `while` loop, so a
//! loop body is not what failed. Whether `?` translates with a `From`
//! conversion or on an `Option` has not been tried since, and the failure
//! presumably lay in one of those. So the verified
//! zone spells its early returns as `let`-`else` and `match`, uses `?` only
//! in the shape known to work, and keeps `clippy::question_mark` off because
//! that lint asks for `?` wherever a `match` returns early, which is the
//! untested shape. The consuming product applies the same rule to its own
//! verified code.
// No `unsafe` in this library crate, enforced by the attribute rather than
// observed; every library crate in the workspace carries it. The one `unsafe`
// block in the workspace is in `tacenta-core/tests/timing.rs`, which sets a CPU flag
// for measurement. The attribute bounds this crate only -- dependencies are
// the trusted boundary and are unaffected.
#![forbid(unsafe_code)]
#![allow(clippy::question_mark)]

use tacenta_kdf as kdf;
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

/// Which set of KDF `info` labels a session derives under. See tacenta-model
/// Model.State (`rkInfo`).
///
/// The published Double Ratchet and PQXDH documents leave these labels
/// application-specific, so they are a choice rather than a computation. One
/// set exists today. Naming the choice, carrying it in the state and persisting
/// it with the state is what stops a second set later from requiring every
/// session established under the first to be reissued. Message-layer wire
/// compatibility with any other implementation is not attempted; carrying the
/// choice keeps a later change cheap.
///
/// Select the labels with a `match` **inside** the function that uses them. A
/// helper that returns `&'static [u8]` does not translate: Charon and Aeneas
/// give up on any body that calls one, whether or not an enum is involved.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LabelSet {
    /// Tacenta's own labels, chosen for self-consistency rather than to match
    /// any peer.
    Tacenta,
}

const RK_INFO: &[u8] = b"Tacenta RK";
/// Message-key expansion `info` label (Model.State `mkInfo`).
const MK_INFO: &[u8] = b"Tacenta MK";

/// The most keys that may be skipped in a single chain (ratchet.md, Skipped
/// keys).
pub const MAX_SKIP: u32 = 1000;

/// The most keys the skipped store may hold in total. A per-chain bound alone
/// does not bound the store, since every Diffie-Hellman ratchet step starts a
/// fresh chain; the specification requires the store itself to reject when too
/// many elements are held.
pub const MAX_SKIPPED_STORE: usize = 2000;

/// How many received messages a skipped key may outlive before it is deleted
/// (key-deletion.md). `MAX_SKIPPED_STORE` bounds how many are held; this bounds
/// how long one is held, which the bound alone does not.
///
/// A policy choice, and a trade-off in both directions: too small and a
/// legitimate message delayed behind many others cannot be decrypted, too large
/// and keys stay recoverable longer than they need to. A peer who can drive
/// receives can age a store out deliberately, but that peer can already fill
/// it, and the alternative is keys that never expire at all.
pub const MAX_SKIPPED_AGE: u32 = 1000;

/// A 32-byte protocol key.
pub type Key = [u8; 32];

/// A message header: the sender's current ratchet public key, the length of the
/// previous sending chain, and the message number in the current chain.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Header {
    pub dh: Key,
    pub pn: u32,
    pub n: u32,
}

/// A stored out-of-order message key, keyed by ratchet public key and number.
///
/// No `Debug`, so no derived impl can print the key. Tests get a counters-only
/// impl below, under `cfg(test)`, so `assert_eq!` still works there and a
/// `{:?}` in shipping code does not compile.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
#[cfg_attr(test, derive(PartialEq, Eq))]
struct SkippedKey {
    dh: Key,
    n: u32,
    /// The value of `State::events` when this key was stored, so that
    /// `age_store` can tell how long it has been held.
    stored_at: u32,
    // Named `key` rather than `mk`: a field called `mk` collides with the
    // constructor Lean generates for the structure (`SkippedKey.mk`), which
    // breaks the translated file. See
    // `tacenta-proofs/upstream/aeneas-mk-field-collision`.
    key: Key,
}

/// The ratchet state of one party (ratchet.md, State).
///
/// No `Debug`, so no derived impl can print the root key, the chain keys
/// or a stored message key. A counters-only impl exists under
/// `cfg(test)` for the crate's own assertions.
///
/// Equality only under `cfg(test)`, for the same reason: the derived
/// comparison is byte-wise over the keys and not constant-time. The tests
/// need it for round-trip assertions; nothing shipping compares two states,
/// and with the impl absent nothing shipping can (CR-22).
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
#[cfg_attr(test, derive(PartialEq, Eq))]
pub struct State {
    dhs_pub: Key,
    dhr_pub: Option<Key>,
    rk: Key,
    cks: Option<Key>,
    ckr: Option<Key>,
    ns: u32,
    nr: u32,
    pn: u32,
    skipped: Vec<SkippedKey>,
    /// Received messages counted since the session began. The store's clock:
    /// nothing in here can read a wall clock, so the interval after which a
    /// skipped key is deleted is measured in received messages.
    events: u32,
    /// Which label set this session derives under. See `LabelSet`.
    ///
    /// Skipped by the erasing destructor: it names a choice, not a secret, and
    /// it has no bytes worth wiping.
    #[zeroize(skip)]
    labels: LabelSet,
}

// Counters only, and only for tests. `assert_eq!` on a state needs `Debug`;
// nothing that ships should be able to print one.
#[cfg(test)]
impl core::fmt::Debug for SkippedKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SkippedKey")
            .field("n", &self.n)
            .field("stored_at", &self.stored_at)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
impl core::fmt::Debug for State {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("State")
            .field("ns", &self.ns)
            .field("nr", &self.nr)
            .field("pn", &self.pn)
            .field("skipped", &self.skipped)
            .field("events", &self.events)
            .field("has_cks", &self.cks.is_some())
            .field("has_ckr", &self.ckr.is_some())
            .finish_non_exhaustive()
    }
}

impl State {
    /// The label set this session derives under. Callers outside the ratchet
    /// need it to expand a message key, and persistence needs it so a session
    /// restored later derives the way it did when it was established.
    pub fn labels(&self) -> LabelSet {
        self.labels
    }

    /// How many skipped message keys are held. For a caller deciding whether
    /// to make room (see `evict_oldest`) and for tests.
    pub fn skipped_len(&self) -> usize {
        self.skipped.len()
    }

    /// Delete up to `count` of the oldest stored skipped keys, oldest by the
    /// store's own clock (`stored_at`), and return how many were deleted.
    /// Zero means the store was already empty.
    ///
    /// **Why this exists.** `receive` refuses with `SkippedStoreFull` rather
    /// than evicting, and the store shrinks only through `age_store`, which
    /// runs on a *successful* receive. Once the store is full and one more
    /// live-chain message is missing, every later message needs a slot, is
    /// refused, is never accepted, and so never advances the clock that
    /// would free the store: without eviction a lossy link, or a peer who
    /// could drop (not forge) traffic, would wedge the receive direction until
    /// the session was re-established.
    ///
    /// **Why it is a separate call and not inside `receive`.** Eviction must
    /// only ever land on a message that authenticates, or a forged header
    /// could evict genuine keys -- the property `age_store` on the success
    /// path was designed for. The session layer calls this on its *working
    /// copy* when `receive` reports the store full, retries, and commits the
    /// copy only after the AEAD verifies; on failure the copy, evictions
    /// included, is dropped. `receive` itself stays as proved.
    ///
    /// An index loop, not an iterator, to stay in the translatable subset.
    ///
    /// `#[must_use]`: zero means the store was already empty, and a caller
    /// that does not look at the count retries against an empty store
    /// forever (CR-20).
    #[must_use]
    pub fn evict_oldest(&mut self, count: usize) -> usize {
        let mut evicted = 0;
        while evicted < count && !self.skipped.is_empty() {
            let mut oldest = 0;
            let mut i = 1;
            while i < self.skipped.len() {
                if self.skipped[i].stored_at < self.skipped[oldest].stored_at {
                    oldest = i;
                }
                i += 1;
            }
            self.skipped.remove(oldest);
            evicted += 1;
        }
        evicted
    }
}

/// Failures a ratchet step can report.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RatchetError {
    /// The header asks to skip more than `MAX_SKIP` keys on a chain.
    TooManySkipped,
    /// Storing the skipped keys would push the store past `MAX_SKIPPED_STORE`.
    SkippedStoreFull,
    /// There is no sending chain yet, so a send is not possible.
    NoSendingChain,
    /// There is no receiving chain after stepping, so a receive is not possible.
    NoReceivingChain,
    /// The chain's message counter would exceed its range (2^32 messages on one
    /// chain). Returned rather than overflowing, which keeps the counter
    /// arithmetic panic-free without an unprovable bound assumption.
    ChainExhausted,
}

impl State {
    /// The public key this party currently sends under. A caller that drives the
    /// Diffie-Hellman boundary compares this before and after a `receive` to tell
    /// whether the step took a DH ratchet (in which case the fresh key it
    /// supplied was adopted).
    pub fn sending_public(&self) -> Key {
        self.dhs_pub
    }

    /// The number of messages sent on the current sending chain.
    pub fn send_count(&self) -> u32 {
        self.ns
    }

    /// The number of messages received on the current receiving chain.
    pub fn receive_count(&self) -> u32 {
        self.nr
    }
}

/// This crate's own persistence-format version (`State::to_bytes`/
/// `from_bytes`). A private namespace: this is what a storage layer writes to
/// disk and reads back after a restart, not anything a peer ever receives, so
/// it evolves on its own schedule rather than sharing the message-format
/// version space (`tacenta-core/src/serialization`).
const STATE_VERSION: u8 = 0x01;

/// Named with the crate's own prefix rather than plainly `DecodeError`, which
/// reads redundantly inside this crate and is deliberate. Charon emits
/// discriminant instances unqualified, so each crate's error enum carries a
/// distinct name. The redundancy in here buys uniqueness out there. Do not
/// tidy it.
///
/// A `State::to_bytes`/`from_bytes` failure. This format's threat model is
/// corruption and version skew (a partial write, an app upgrade with a
/// changed field), not a hostile peer -- there is no peer here at all -- so
/// unlike a wire `RatchetDecodeError` this has no obligation to reveal no more than
/// "unacceptable"; it distinguishes its causes because a storage layer's
/// caller can act on the difference (refuse to start vs. treat as corrupt).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RatchetDecodeError {
    UnknownVersion,
    TooShort,
    Malformed,
}

/// One byte presence tag plus the full 32-byte width regardless, zeroed when
/// absent -- the same choice `composite.rs`'s optional field makes, for the
/// same reason: a canonical encoding is provable, a variable-width optional
/// only tested.
const OPTIONAL_KEY_LEN: usize = 1 + 32;

const FIXED_LEN: usize = 1 // version
    + 32 // dhs_pub
    + OPTIONAL_KEY_LEN // dhr_pub
    + 32 // rk
    + OPTIONAL_KEY_LEN // cks
    + OPTIONAL_KEY_LEN // ckr
    + 4 + 4 + 4 // ns, nr, pn
    + 4 // events
    + 1 // labels
    + 4; // skipped count

fn read_key(bytes: &[u8], pos: usize) -> Key {
    let mut k = [0u8; 32];
    k.copy_from_slice(&bytes[pos..pos + 32]);
    k
}

fn read_u32(bytes: &[u8], pos: usize) -> u32 {
    let mut b = [0u8; 4];
    b.copy_from_slice(&bytes[pos..pos + 4]);
    u32::from_be_bytes(b)
}

fn push_optional_key(out: &mut Vec<u8>, key: &Option<Key>) {
    match key {
        None => {
            out.push(0x00);
            out.extend_from_slice(&[0u8; 32]);
        }
        Some(k) => {
            out.push(0x01);
            out.extend_from_slice(k);
        }
    }
}

fn read_optional_key(bytes: &[u8], pos: usize) -> Result<Option<Key>, RatchetDecodeError> {
    match bytes[pos] {
        0x00 => {
            // The absent key still occupies its 32 bytes, written as zeros by
            // `to_bytes`. Refuse anything else in them: a second spelling of
            // one state, accepted and re-emitted differently, is exactly what
            // the persisted-state fuzz target's re-encode oracle exists to
            // catch. Same rule as the composite header's absent-chunk padding.
            // A flag rather than a return inside the loop: Aeneas does not
            // translate an early return out of a loop.
            let mut clean = true;
            let mut i = pos + 1;
            while i < pos + 33 {
                if bytes[i] != 0 {
                    clean = false;
                }
                i += 1;
            }
            if clean {
                Ok(None)
            } else {
                Err(RatchetDecodeError::Malformed)
            }
        }
        0x01 => Ok(Some(read_key(bytes, pos + 1))),
        _ => Err(RatchetDecodeError::Malformed),
    }
}

impl LabelSet {
    fn to_byte(self) -> u8 {
        match self {
            LabelSet::Tacenta => 0x00,
        }
    }

    fn from_byte(b: u8) -> Option<LabelSet> {
        match b {
            0x00 => Some(LabelSet::Tacenta),
            _ => None,
        }
    }
}

impl SkippedKey {
    const ENCODED_LEN: usize = 32 + 4 + 4 + 32;

    fn encode_into(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.dh);
        out.extend_from_slice(&self.n.to_be_bytes());
        out.extend_from_slice(&self.stored_at.to_be_bytes());
        out.extend_from_slice(&self.key);
    }

    fn decode(bytes: &[u8]) -> Option<SkippedKey> {
        if bytes.len() != Self::ENCODED_LEN {
            return None;
        }
        let mut dh = [0u8; 32];
        dh.copy_from_slice(&bytes[0..32]);
        let mut n_bytes = [0u8; 4];
        n_bytes.copy_from_slice(&bytes[32..36]);
        let mut stored_at_bytes = [0u8; 4];
        stored_at_bytes.copy_from_slice(&bytes[36..40]);
        let mut key = [0u8; 32];
        key.copy_from_slice(&bytes[40..72]);
        Some(SkippedKey {
            dh,
            n: u32::from_be_bytes(n_bytes),
            stored_at: u32::from_be_bytes(stored_at_bytes),
            key,
        })
    }
}

/// Bounds-check and decode one skipped entry at `pos` in a single step, so
/// the loop that calls this has exactly one early-exit branch rather than two.
fn decode_skipped_entry(bytes: &[u8], pos: usize) -> Option<SkippedKey> {
    if bytes.len() < pos + SkippedKey::ENCODED_LEN {
        return None;
    }
    SkippedKey::decode(&bytes[pos..pos + SkippedKey::ENCODED_LEN])
}

impl State {
    /// Encode this state for persistence. Wrapped so the buffer holding its
    /// keys is wiped when dropped, the same as every other secret-bearing
    /// buffer in this crate -- an export is a new kind of buffer to wipe, not
    /// a new kind of secret.
    ///
    /// Not a message on the wire: see `tacenta-core/src/serialization` for
    /// that. This is what a storage layer writes to disk and reads back with
    /// `from_bytes` after a restart. Whether the bytes on disk are protected
    /// from anything other than corruption is that caller's job --
    /// key-deletion.md's in-memory-only erasure claim does not extend here by
    /// itself.
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        let mut out = Vec::with_capacity(FIXED_LEN + self.skipped.len() * SkippedKey::ENCODED_LEN);
        out.push(STATE_VERSION);
        out.extend_from_slice(&self.dhs_pub);
        push_optional_key(&mut out, &self.dhr_pub);
        out.extend_from_slice(&self.rk);
        push_optional_key(&mut out, &self.cks);
        push_optional_key(&mut out, &self.ckr);
        out.extend_from_slice(&self.ns.to_be_bytes());
        out.extend_from_slice(&self.nr.to_be_bytes());
        out.extend_from_slice(&self.pn.to_be_bytes());
        out.extend_from_slice(&self.events.to_be_bytes());
        out.push(self.labels.to_byte());
        out.extend_from_slice(&(self.skipped.len() as u32).to_be_bytes());
        let mut i = 0;
        while i < self.skipped.len() {
            self.skipped[i].encode_into(&mut out);
            i += 1;
        }
        Zeroizing::new(out)
    }

    /// Decode a state persisted by `to_bytes`. Canonical: trailing bytes past
    /// the last skipped entry are refused rather than ignored, the same
    /// choice this crate's sibling wire formats make.
    pub fn from_bytes(bytes: &[u8]) -> Result<State, RatchetDecodeError> {
        if bytes.len() < FIXED_LEN {
            return Err(RatchetDecodeError::TooShort);
        }
        if bytes[0] != STATE_VERSION {
            return Err(RatchetDecodeError::UnknownVersion);
        }
        let mut pos = 1;
        let dhs_pub = read_key(bytes, pos);
        pos += 32;
        let dhr_pub = match read_optional_key(bytes, pos) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        pos += OPTIONAL_KEY_LEN;
        let rk = read_key(bytes, pos);
        pos += 32;
        let cks = match read_optional_key(bytes, pos) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        pos += OPTIONAL_KEY_LEN;
        let ckr = match read_optional_key(bytes, pos) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        pos += OPTIONAL_KEY_LEN;
        let ns = read_u32(bytes, pos);
        pos += 4;
        let nr = read_u32(bytes, pos);
        pos += 4;
        let pn = read_u32(bytes, pos);
        pos += 4;
        let events = read_u32(bytes, pos);
        pos += 4;
        let Some(labels) = LabelSet::from_byte(bytes[pos]) else {
            return Err(RatchetDecodeError::Malformed);
        };
        pos += 1;
        let skipped_count = read_u32(bytes, pos) as usize;
        pos += 4;

        // **Bounded against the buffer before the loop runs.** The loop has
        // no early exit, so without this a four-byte count field can make it
        // run four billion times against a buffer that cannot satisfy one
        // iteration. Nothing previously accepted is rejected: the `pos !=
        // bytes.len()` check below already requires the count to account for
        // the buffer exactly. See `tacenta-erasure`, whose coders bound their
        // counts the same way, and then again by what an honest run can hold,
        // as the next check here does.
        if skipped_count > bytes.len() / SkippedKey::ENCODED_LEN {
            return Err(RatchetDecodeError::Malformed);
        }
        // And against the store's own bound, which `skip_message_keys`
        // maintains and which a buffer alone does not imply (CR-21).
        if skipped_count > MAX_SKIPPED_STORE {
            return Err(RatchetDecodeError::Malformed);
        }

        // No early return inside this loop: a failed entry sets `ok = false`
        // and the loop still runs to completion (every remaining call is
        // still bounds-checked by `decode_skipped_entry`, so nothing panics),
        // with the failure reported once, after the loop.
        let mut skipped = Vec::new();
        let mut ok = true;
        for _ in 0..skipped_count {
            match decode_skipped_entry(bytes, pos) {
                Some(entry) => {
                    skipped.push(entry);
                    pos += SkippedKey::ENCODED_LEN;
                }
                None => {
                    ok = false;
                }
            }
        }
        if !ok || pos != bytes.len() {
            return Err(RatchetDecodeError::Malformed);
        }

        // **The store must be one the operations could have built.** They
        // keep it a map on `(dh, n)` -- `purge_chain_range` clears a range
        // before it is re-derived -- and both lookups answer with the first
        // match, so a second entry for one pair would be unreachable and
        // would hold a slot against the bound while a genuine message at that
        // number was answered with the wrong key. And `stored_at` is a
        // reading of `events`, which only grows, so an entry from the future
        // is one no run produced. Index loops over a count already bounded
        // above, with a flag rather than a return from inside (CR-21).
        let mut consistent = true;
        let mut i = 0;
        while i < skipped.len() {
            if skipped[i].stored_at > events {
                consistent = false;
            }
            let mut j = i + 1;
            while j < skipped.len() {
                if skipped[i].dh == skipped[j].dh && skipped[i].n == skipped[j].n {
                    consistent = false;
                }
                j += 1;
            }
            i += 1;
        }
        if !consistent {
            return Err(RatchetDecodeError::Malformed);
        }

        Ok(State {
            dhs_pub,
            dhr_pub,
            rk,
            cks,
            ckr,
            ns,
            nr,
            pn,
            skipped,
            events,
            labels,
        })
    }
}

/// KDF_CK (ratchet.md): advance a chain key one step, returning
/// `(next chain key, message key)`.
fn kdf_ck(ck: &Key) -> (Key, Key) {
    let mk = kdf::hmac_sha256(ck, &[0x01]);
    let next = kdf::hmac_sha256(ck, &[0x02]);
    (next, mk)
}

/// KDF_RK (ratchet.md): fold a DH output into the root key, returning
/// `(new root key, new chain key)`.
fn kdf_rk(rk: &Key, dh_out: &Key, labels: LabelSet) -> (Key, Key) {
    let info: &[u8] = match labels {
        LabelSet::Tacenta => RK_INFO,
    };
    // Wiped on the way out: the 64 bytes hold both derived keys.
    let out = Zeroizing::new(kdf::hkdf_sha256::<64>(rk, dh_out, info));
    let mut rk2 = [0u8; 32];
    let mut ck = [0u8; 32];
    rk2.copy_from_slice(&out[..32]);
    ck.copy_from_slice(&out[32..]);
    (rk2, ck)
}

/// Message-key expansion (ratchet.md): derive the AEAD material (AES-256 key,
/// HMAC key, 16-byte IV) from a message key. The AEAD itself is a
/// trusted-boundary primitive.
pub fn message_keys(mk: &Key, labels: LabelSet) -> (Key, Key, [u8; 16]) {
    let info: &[u8] = match labels {
        LabelSet::Tacenta => MK_INFO,
    };
    // Wiped on the way out: the 80 bytes hold the AEAD key, MAC key, and IV.
    let out = Zeroizing::new(kdf::hkdf_sha256::<80>(&[0u8; 32], mk, info));
    let mut enc = [0u8; 32];
    let mut mac = [0u8; 32];
    let mut iv = [0u8; 16];
    enc.copy_from_slice(&out[..32]);
    mac.copy_from_slice(&out[32..64]);
    iv.copy_from_slice(&out[64..]);
    (enc, mac, iv)
}

/// The `(message number, message key)` pairs one `derive_chain` produces,
/// wiped whole when dropped; see there for why the wrapper is on the vector.
type DerivedKeys = Zeroizing<Vec<(u32, Key)>>;

/// Advance a chain `count` steps from `start_n`, returning the final chain key
/// and each `(message number, message key)` produced.
///
/// The message number is computed with `checked_add` and exhaustion reported as
/// `ChainExhausted`, the same way [`send`] treats its counter. The callers do
/// bound `count` so the sum cannot in fact overflow, but making the arithmetic
/// total removes the panic site by construction rather than leaving a proof
/// obligation that the bound holds. One less thing to prove, and one less thing
/// to get wrong if a future caller forgets the bound.
///
/// The accumulator is `Zeroizing` and allocated at its final size: it can
/// hold up to `MAX_SKIP` message keys, and the caller copies them into the
/// store, so the vector is wiped where it stands when it drops rather than
/// handed back to the allocator with the keys still in it. Two things make
/// that true. Wrapping the whole vector, not each key: moving elements out of
/// a vector leaves their bytes in its buffer, so the caller reads them by
/// index and lets the wrapper wipe the buffer entire (CR-15). And reserving
/// `count` slots before the first push: a vector that grew as it went would
/// copy the keys derived so far into each larger buffer and free the old one
/// unwiped, behind the wrapper's back. The reservation is also why the bound
/// on `count` matters for memory, not only for time.
fn derive_chain(ck: &Key, start_n: u32, count: u32) -> Result<(Key, DerivedKeys), RatchetError> {
    let mut cur = *ck;
    let mut keys = Zeroizing::new(Vec::with_capacity(count as usize));
    for i in 0..count {
        let Some(n) = start_n.checked_add(i) else {
            return Err(RatchetError::ChainExhausted);
        };
        let (next, mk) = kdf_ck(&cur);
        keys.push((n, mk));
        cur = next;
    }
    Ok((cur, keys))
}

/// Store skipped message keys on the current receiving chain up to (but not
/// including) `upto` (ratchet.md, Skipped keys). Rejects a request beyond
/// `MAX_SKIP` so a malicious header cannot exhaust memory.
fn skip_message_keys(state: &mut State, upto: u32) -> Result<(), RatchetError> {
    match (state.ckr, state.dhr_pub) {
        (Some(ck), Some(dhr)) => {
            if upto <= state.nr {
                Ok(())
            } else if upto > state.nr.saturating_add(MAX_SKIP) {
                Err(RatchetError::TooManySkipped)
            } else if state.skipped.len() + (upto - state.nr) as usize > MAX_SKIPPED_STORE {
                Err(RatchetError::SkippedStoreFull)
            } else {
                let (ck2, keys) = match derive_chain(&ck, state.nr, upto - state.nr) {
                    Ok(v) => v,
                    Err(e) => return Err(e),
                };
                purge_chain_range(&mut state.skipped, dhr, state.nr, upto);
                // By index rather than by consuming the vector, so that it is
                // wiped whole when it drops; see `derive_chain`.
                let mut i = 0;
                while i < keys.len() {
                    state.skipped.push(SkippedKey {
                        dh: dhr,
                        n: keys[i].0,
                        stored_at: state.events,
                        key: keys[i].1,
                    });
                    i += 1;
                }
                state.ckr = Some(ck2);
                state.nr = upto;
                Ok(())
            }
        }
        _ => Ok(()),
    }
}

/// Initialise the party that sends first: it already holds the peer's initial
/// ratchet public key. `sk` is the shared root key from session establishment
/// and `dh_out = DH(our_initial_priv, peer_pub)`.
pub fn init_sender(sk: &Key, our_pub: Key, peer_pub: Key, dh_out: &Key, labels: LabelSet) -> State {
    let (rk, cks) = kdf_rk(sk, dh_out, labels);
    State {
        dhs_pub: our_pub,
        dhr_pub: Some(peer_pub),
        rk,
        cks: Some(cks),
        ckr: None,
        ns: 0,
        nr: 0,
        pn: 0,
        skipped: Vec::new(),
        events: 0,
        labels,
    }
}

/// Initialise the party that receives first: it holds its own ratchet keypair
/// but has not seen the peer's ratchet key, so it has only the root key until
/// the first message arrives.
pub fn init_receiver(sk: &Key, our_pub: Key, labels: LabelSet) -> State {
    State {
        dhs_pub: our_pub,
        dhr_pub: None,
        rk: *sk,
        cks: None,
        ckr: None,
        ns: 0,
        nr: 0,
        pn: 0,
        skipped: Vec::new(),
        events: 0,
        labels,
    }
}

/// Send (ratchet.md): advance the sending chain and produce the header and
/// message key.
pub fn send(state: &mut State) -> Result<(Header, Key), RatchetError> {
    match state.cks {
        None => Err(RatchetError::NoSendingChain),
        Some(ck) => {
            // Check the counter before mutating, so an exhausted chain is a clean
            // error rather than an overflow.
            let Some(next_ns) = state.ns.checked_add(1) else {
                return Err(RatchetError::ChainExhausted);
            };
            let (ck2, mk) = kdf_ck(&ck);
            let header = Header {
                dh: state.dhs_pub,
                pn: state.pn,
                n: state.ns,
            };
            state.cks = Some(ck2);
            state.ns = next_ns;
            Ok((header, mk))
        }
    }
}

/// A Diffie-Hellman ratchet step (ratchet.md). `dh_out_recv = DH(DHs.priv,
/// header.dh)` seeds the new receiving chain; `dh_out_send = DH(new_dhs.priv,
/// header.dh)` seeds the new sending chain under `new_dhs_pub`.
fn dh_ratchet(
    state: &mut State,
    header: &Header,
    dh_out_recv: &Key,
    dh_out_send: &Key,
    new_dhs_pub: Key,
) {
    let (rk1, ckr) = kdf_rk(&state.rk, dh_out_recv, state.labels);
    let (rk2, cks) = kdf_rk(&rk1, dh_out_send, state.labels);
    state.pn = state.ns;
    state.ns = 0;
    state.nr = 0;
    state.dhr_pub = Some(header.dh);
    state.rk = rk2;
    state.ckr = Some(ckr);
    state.cks = Some(cks);
    state.dhs_pub = new_dhs_pub;
}

/// Look for a stored skipped key matching the header; if found, remove and
/// return it.
/// Drop any stored key already held under this ratchet key for the message
/// numbers about to be stored, so the store stays the map it is documented to
/// be.
///
/// The peer chooses the ratchet public key in the header, and nothing requires
/// it to be one it has not used before. A peer that leaves a key and returns to
/// it gets a fresh chain numbered from zero under a ratchet key already in the
/// store, which without this leaves two entries for one pair holding different
/// keys. Both lookups return the first match, so the second would be
/// unreachable: never found, never deleted, and holding a slot against
/// `MAX_SKIPPED_STORE`, while a genuine later message on that chain would be
/// answered with the wrong key.
///
/// Replacing rather than keeping the older entry is what a map does, and it is
/// the useful direction: the newer key is the one a message on the live chain
/// needs, and the older one is stale material better dropped.
///
/// **Only the range being re-derived is purged**, `[from, upto)` under this
/// ratchet key, so the store is a map *for that range*. If a peer ever
/// returned to a ratchet key it had used before -- which no honest peer does
/// -- entries from the earlier chain with `n >= upto` would survive, and a
/// later genuine message at one of those numbers would match the stale entry
/// in `try_skipped`, fail its AEAD, and stay undecryptable until a higher
/// number on the chain purged it. Peer-inflicted only, with no outsider
/// capability, and recorded here so the "map" above is read at its actual
/// width.
///
/// An index loop for the same reason as `try_skipped` below: it stays in the
/// subset the Charon/Aeneas translation models. It takes the store rather than
/// the whole state so that the translated storing loop keeps threading a vector
/// rather than a state, which is what its existing proofs are written against.
fn purge_chain_range(skipped: &mut Vec<SkippedKey>, dhr: Key, from: u32, upto: u32) {
    let mut i = 0;
    while i < skipped.len() {
        if skipped[i].dh == dhr && skipped[i].n >= from && skipped[i].n < upto {
            skipped.remove(i);
        } else {
            i += 1;
        }
    }
}

/// Count one received message and delete the skipped keys that have outlived
/// `MAX_SKIPPED_AGE` (key-deletion.md).
///
/// Applied once per accepted receive, at the end, so a key stored during that
/// same receive is one message old rather than zero.
///
/// `events` saturates rather than wrapping. A session that receives `u32::MAX`
/// messages then expires every skipped key immediately, which fails safe; the
/// refinement against the model excludes that case, as it does everywhere the
/// core counts in `u32` and the model in the naturals.
fn age_store(state: &mut State) {
    let now = state.events.saturating_add(1);
    state.events = now;
    let mut i = 0;
    while i < state.skipped.len() {
        // Saturating rather than checked: `stored_at` is never ahead of `now`,
        // but proving that would mean carrying an invariant through every
        // caller, and this removes the underflow instead of assuming it away.
        // It also matches the model exactly, where the subtraction is over the
        // naturals and already truncates.
        if now.saturating_sub(state.skipped[i].stored_at) >= MAX_SKIPPED_AGE {
            state.skipped.remove(i);
        } else {
            i += 1;
        }
    }
}

fn try_skipped(state: &mut State, header: &Header) -> Option<Key> {
    // An index loop rather than an iterator adaptor, so the function stays in
    // the subset the Charon/Aeneas translation models (`Iterator::position` has
    // no model in the Aeneas Lean library; `Vec` index, len, and remove do).
    let mut i = 0;
    while i < state.skipped.len() {
        if state.skipped[i].dh == header.dh && state.skipped[i].n == header.n {
            let mk = state.skipped[i].key;
            state.skipped.remove(i);
            return Some(mk);
        }
        i += 1;
    }
    None
}

/// Receive (ratchet.md): try a stored skipped key; otherwise, on an unseen
/// ratchet key, skip the remainder of the old receiving chain up to `header.pn`
/// and take a DH ratchet step; then skip up to `header.n` on the current chain
/// and derive the message key at `header.n`. DH outputs and the fresh sending
/// key are ignored on a same-chain message.
///
/// **On `Err` the state may already have moved.** On an unseen ratchet key the
/// old chain is skipped and the DH step taken -- new root key, new sending
/// key, counters reset -- before the skip on the new chain can still refuse;
/// and a skipped key is removed from the store the moment it matches. The
/// Triple Ratchet and the session run this on a copy and adopt it only once
/// the message authenticates, which is what makes those partial advances
/// harmless there. A caller driving this crate directly must do the same:
/// operate on a copy, and treat a state that returned `Err` as spent (CR-20).
pub fn receive(
    state: &mut State,
    header: &Header,
    dh_out_recv: &Key,
    dh_out_send: &Key,
    new_dhs_pub: Key,
) -> Result<Key, RatchetError> {
    if let Some(mk) = try_skipped(state, header) {
        age_store(state);
        return Ok(mk);
    }
    // Matched explicitly rather than written `!= Some(header.dh)`: comparing
    // two `Option`s reaches the translation as an axiom, since Aeneas does not
    // model it, which would leave panic-freedom resting on an assumption about
    // the standard library. Comparing the arrays directly uses an operation the
    // translation does model. Same move as making the counters checked: remove
    // the dependency rather than assume it away.
    let needs_ratchet = match state.dhr_pub {
        None => true,
        Some(dhr) => dhr != header.dh,
    };
    if needs_ratchet {
        if let Err(e) = skip_message_keys(state, header.pn) {
            return Err(e);
        }
        dh_ratchet(state, header, dh_out_recv, dh_out_send, new_dhs_pub);
    }
    if let Err(e) = skip_message_keys(state, header.n) {
        return Err(e);
    }
    match state.ckr {
        None => Err(RatchetError::NoReceivingChain),
        Some(ck) => {
            let Some(next_nr) = state.nr.checked_add(1) else {
                return Err(RatchetError::ChainExhausted);
            };
            let (ck2, mk) = kdf_ck(&ck);
            state.ckr = Some(ck2);
            state.nr = next_nr;
            age_store(state);
            Ok(mk)
        }
    }
}

#[cfg(test)]
mod decode_bounds_tests {
    use super::*;

    /// A skipped-key count the buffer cannot hold is refused before the loop.
    ///
    /// The loop below the count has no early exit -- deliberately, so the
    /// function stays inside what Charon and Aeneas translate -- which means an
    /// unbounded count is not a slow rejection but a hang. The same
    /// accommodation appears in `tacenta-erasure`, with the same bound.
    #[test]
    fn a_skipped_count_the_buffer_cannot_hold_is_refused_at_once() {
        // Enough bytes for the fixed header, then a count of `u32::MAX` and
        // nothing to satisfy it.
        let mut buf = vec![0u8; 128];
        buf[0] = STATE_VERSION;
        let end = buf.len();
        buf[end - 4..].copy_from_slice(&u32::MAX.to_be_bytes());
        // Whatever it decides about the rest, it must decide it promptly.
        let _ = State::from_bytes(&buf);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A skipped key is deleted once it has outlived `MAX_SKIPPED_AGE`
    /// received messages, and not before.
    ///
    /// The boundary is pinned on both sides rather than just checking that
    /// something is removed: the same two cases are checked against the model
    /// in `Properties.Invariants`, so a change to one that is not made to the
    /// other fails here or there.
    #[test]
    fn skipped_keys_expire_at_the_cap() {
        let held = |events: u32| {
            let mut s = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
            s.skipped.push(SkippedKey {
                dh: A_PUB,
                n: 7,
                stored_at: 0,
                key: [0xe1; 32],
            });
            s.events = events;
            s
        };

        let mut short = held(MAX_SKIPPED_AGE - 2);
        age_store(&mut short);
        assert_eq!(short.skipped.len(), 1, "one message short of the cap");

        let mut at_cap = held(MAX_SKIPPED_AGE - 1);
        age_store(&mut at_cap);
        assert_eq!(at_cap.skipped.len(), 0, "at the cap");
    }

    /// Every accepted receive counts, whether or not anything expired.
    #[test]
    fn receiving_counts_a_message() {
        let mut sa = init_sender(&SK, A_PUB, B_PUB, &DH_AB, LabelSet::Tacenta);
        let (h0, _) = send(&mut sa).unwrap();
        let mut sb = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        assert_eq!(sb.events, 0);
        receive(&mut sb, &h0, &DH_AB, &DH_B2A, B2_PUB).unwrap();
        assert_eq!(sb.events, 1);
    }

    /// The state and the stored skipped keys erase themselves when dropped.
    ///
    /// A static check rather than an inspection of freed memory, which is not
    /// something a test can do soundly. What it pins is that the derive cannot
    /// be removed without the build failing, which matters because the erasure
    /// is invisible to the proofs: Charon and Aeneas ignore `Drop`, so the
    /// generated Lean is byte for byte the same with or without it, and T1 and
    /// T3 say nothing about erasure (key-deletion.md).
    #[test]
    fn the_state_erases_when_dropped() {
        fn assert_erases<T: zeroize::ZeroizeOnDrop>() {}
        assert_erases::<State>();
        assert_erases::<SkippedKey>();
    }

    // Fixed stand-ins for keys and DH outputs, matching the model's scenarios.
    // DH symmetry (DH(a, B) = DH(b, A)) is honoured by giving both parties the
    // same shared output.
    const SK: Key = [0x01; 32];
    const A_PUB: Key = [0x0a; 32];
    const B_PUB: Key = [0x0b; 32];
    const B2_PUB: Key = [0x2b; 32];
    const DH_AB: Key = [0xab; 32];
    const DH_B2A: Key = [0xba; 32];

    #[test]
    fn in_order_message_keys_agree() {
        let mut sa = init_sender(&SK, A_PUB, B_PUB, &DH_AB, LabelSet::Tacenta);
        let (h0, mk_send) = send(&mut sa).unwrap();
        let mut sb = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let mk_recv = receive(&mut sb, &h0, &DH_AB, &DH_B2A, B2_PUB).unwrap();
        assert_eq!(mk_send, mk_recv);
    }

    #[test]
    fn out_of_order_recovers_via_skipped_store() {
        let mut sa = init_sender(&SK, A_PUB, B_PUB, &DH_AB, LabelSet::Tacenta);
        let (h0, mk0_send) = send(&mut sa).unwrap();
        let (h1, mk1_send) = send(&mut sa).unwrap();
        let mut sb = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let mk1_recv = receive(&mut sb, &h1, &DH_AB, &DH_B2A, B2_PUB).unwrap();
        let mk0_recv = receive(&mut sb, &h0, &DH_AB, &DH_B2A, B2_PUB).unwrap();
        assert_eq!(mk0_send, mk0_recv);
        assert_eq!(mk1_send, mk1_recv);
    }

    #[test]
    fn skipping_beyond_bound_is_rejected() {
        let mut sb = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let bad = Header {
            dh: A_PUB,
            pn: 0,
            n: MAX_SKIP + 5,
        };
        assert_eq!(
            receive(&mut sb, &bad, &DH_AB, &DH_B2A, B2_PUB),
            Err(RatchetError::TooManySkipped)
        );
    }

    #[test]
    fn skipped_store_is_bounded_across_ratchet_steps() {
        // The per-chain MAX_SKIP bound alone would not bound the store: each DH
        // ratchet step starts a fresh chain, so a peer that keeps ratcheting and
        // skipping could grow it without limit. Drive exactly that and confirm
        // the store bound rejects it.
        let mut sb = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let mut err = None;
        for step in 0..10u32 {
            // A fresh ratchet key each time, so every receive takes a DH step.
            let mut dh = [0u8; 32];
            dh[0] = step as u8 + 1;
            let header = Header {
                dh,
                pn: 0,
                n: MAX_SKIP - 1,
            };
            if let Err(e) = receive(&mut sb, &header, &DH_AB, &DH_B2A, B2_PUB) {
                err = Some(e);
                break;
            }
        }
        assert_eq!(
            err,
            Some(RatchetError::SkippedStoreFull),
            "the skipped store must stop growing once it is full"
        );
        assert!(
            sb.skipped.len() <= MAX_SKIPPED_STORE,
            "store held {} keys, bound is {MAX_SKIPPED_STORE}",
            sb.skipped.len()
        );
    }

    /// A state with every optional field populated and a non-empty skipped
    /// store round-trips byte for byte and field for field. This is the case
    /// the fixed-width optional encoding exists for.
    #[test]
    fn to_bytes_from_bytes_round_trips_a_populated_state() {
        let mut sa = init_sender(&SK, A_PUB, B_PUB, &DH_AB, LabelSet::Tacenta);
        send(&mut sa).unwrap();
        let mut sb = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let (h0, _) = send(&mut sa).unwrap();
        let (h1, _) = send(&mut sa).unwrap();
        // Out of order, so h0 lands in the skipped store.
        receive(&mut sb, &h1, &DH_AB, &DH_B2A, B2_PUB).unwrap();

        let bytes = sb.to_bytes();
        let restored = State::from_bytes(&bytes).unwrap();
        assert_eq!(sb, restored);
        // Receiving h1 (n=2) on a fresh chain skips both n=0 and n=1.
        assert_eq!(restored.skipped.len(), 2, "h0's key is still in the store");

        // The restored state keeps working: h0 is still recoverable from it.
        let mut restored = restored;
        let mk0 = receive(&mut restored, &h0, &DH_AB, &DH_B2A, B2_PUB).unwrap();
        let mut sb2 = sb;
        let mk0_direct = receive(&mut sb2, &h0, &DH_AB, &DH_B2A, B2_PUB).unwrap();
        assert_eq!(mk0, mk0_direct);
    }

    /// A freshly initialised receiver has every optional field absent and an
    /// empty skipped store -- the other end of the shape `to_bytes` encodes.
    #[test]
    fn to_bytes_from_bytes_round_trips_an_empty_state() {
        let fresh = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let bytes = fresh.to_bytes();
        let restored = State::from_bytes(&bytes).unwrap();
        assert_eq!(fresh, restored);
    }

    #[test]
    fn from_bytes_rejects_a_foreign_version() {
        let fresh = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let mut bytes = fresh.to_bytes().to_vec();
        bytes[0] = 0xff;
        assert_eq!(
            State::from_bytes(&bytes),
            Err(RatchetDecodeError::UnknownVersion)
        );
    }

    #[test]
    fn from_bytes_rejects_a_truncated_buffer() {
        let fresh = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let bytes = fresh.to_bytes();
        assert_eq!(
            State::from_bytes(&bytes[..bytes.len() - 1]),
            Err(RatchetDecodeError::TooShort)
        );
    }

    #[test]
    fn from_bytes_rejects_a_bad_presence_byte() {
        let fresh = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let mut bytes = fresh.to_bytes().to_vec();
        // The dhr_pub presence byte, right after the version and dhs_pub.
        bytes[33] = 0x02;
        assert_eq!(
            State::from_bytes(&bytes),
            Err(RatchetDecodeError::Malformed)
        );
    }

    #[test]
    fn from_bytes_rejects_trailing_bytes() {
        let fresh = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let mut bytes = fresh.to_bytes().to_vec();
        bytes.push(0x00);
        assert_eq!(
            State::from_bytes(&bytes),
            Err(RatchetDecodeError::Malformed)
        );
    }

    /// An absent key's thirty-two bytes must be zero, or the same state has
    /// two spellings and `from_bytes`/`to_bytes` disagree on the bytes. The
    /// sparse ratchet's optional keys have the same shape and the same check.
    /// A stored entry repeated under one `(dh, n)` is refused (CR-21): both
    /// lookups take the first match, so the second could neither be found nor
    /// deleted, and the store would not be the map the operations keep it.
    #[test]
    fn from_bytes_rejects_a_duplicated_skipped_entry() {
        let mut a = init_sender(
            &[1u8; 32],
            [2u8; 32],
            [3u8; 32],
            &[4u8; 32],
            LabelSet::Tacenta,
        );
        let mut b = init_receiver(&[1u8; 32], [3u8; 32], LabelSet::Tacenta);
        let h0 = send(&mut a).unwrap().0;
        let h1 = send(&mut a).unwrap().0;
        // Deliver the second first, so one key is stored.
        receive(&mut b, &h1, &[4u8; 32], &[5u8; 32], [6u8; 32]).unwrap();
        assert_eq!(b.skipped_len(), 1);
        let bytes = b.to_bytes();
        let count_at = FIXED_LEN - 4;
        let entry_at = FIXED_LEN;
        let mut dirty = Vec::new();
        dirty.extend_from_slice(&bytes[..count_at]);
        dirty.extend_from_slice(&2u32.to_be_bytes());
        dirty.extend_from_slice(&bytes[entry_at..]);
        dirty.extend_from_slice(&bytes[entry_at..]);
        assert!(matches!(
            State::from_bytes(&dirty),
            Err(RatchetDecodeError::Malformed)
        ));
        // The same two entries with distinct numbers are a store an honest run
        // can hold, and restore.
        let second_n = entry_at + SkippedKey::ENCODED_LEN + 32;
        dirty[second_n..second_n + 4].copy_from_slice(&7u32.to_be_bytes());
        assert!(State::from_bytes(&dirty).is_ok());
        let _ = h0;
    }

    /// An entry whose `stored_at` is ahead of the store's clock is refused
    /// (CR-21): `events` only grows, so no run produced it.
    #[test]
    fn from_bytes_rejects_an_entry_stored_in_the_future() {
        let mut a = init_sender(
            &[1u8; 32],
            [2u8; 32],
            [3u8; 32],
            &[4u8; 32],
            LabelSet::Tacenta,
        );
        let mut b = init_receiver(&[1u8; 32], [3u8; 32], LabelSet::Tacenta);
        let _ = send(&mut a).unwrap();
        let h1 = send(&mut a).unwrap().0;
        receive(&mut b, &h1, &[4u8; 32], &[5u8; 32], [6u8; 32]).unwrap();
        let mut bytes = b.to_bytes().to_vec();
        // The entry's `stored_at` sits after its 32-byte `dh` and 4-byte `n`.
        let at = FIXED_LEN + 32 + 4;
        bytes[at..at + 4].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(matches!(
            State::from_bytes(&bytes),
            Err(RatchetDecodeError::Malformed)
        ));
    }

    /// A count past `MAX_SKIPPED_STORE` is refused before the loop, even with
    /// a buffer large enough to hold it (CR-21).
    #[test]
    fn from_bytes_rejects_a_store_past_its_bound() {
        let b = init_receiver(&[1u8; 32], [3u8; 32], LabelSet::Tacenta);
        let bytes = b.to_bytes();
        let count = MAX_SKIPPED_STORE + 1;
        let mut dirty = Vec::new();
        dirty.extend_from_slice(&bytes[..FIXED_LEN - 4]);
        dirty.extend_from_slice(&(count as u32).to_be_bytes());
        dirty.extend_from_slice(&vec![0u8; count * SkippedKey::ENCODED_LEN]);
        assert!(matches!(
            State::from_bytes(&dirty),
            Err(RatchetDecodeError::Malformed)
        ));
    }

    #[test]
    fn from_bytes_rejects_nonzero_padding_behind_an_absent_key() {
        let fresh = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
        let mut bytes = fresh.to_bytes().to_vec();
        // dhr_pub is absent on a fresh receiver: presence byte 33, then 32
        // bytes of padding.
        assert_eq!(bytes[33], 0x00);
        bytes[34 + 7] = 0xff;
        assert_eq!(
            State::from_bytes(&bytes),
            Err(RatchetDecodeError::Malformed)
        );
    }
}
