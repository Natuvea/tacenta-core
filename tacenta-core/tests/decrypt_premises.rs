//! The runtime form of the premises of the `decrypt_ratchet` refinement, checked on runs the
//! shipped `Session::decrypt` performs. **Tested only, on the inputs tried; this is not a proof.**
//!
//! The Lean refinement of the private `decrypt_ratchet`, which `Session::decrypt` calls for a
//! ratchet frame (`decrypt_ratchet_refines_complete` in
//! `Translation/UnitLifecycleDecryptRatchetT3.lean`, restated as
//! `decrypt_ratchet_refines_of_invariant` in `Translation/UnitLifecycleDecryptRunBounds.lean`),
//! takes, for each call, a per-run record: `RetryRunBounds` (bounds on the Triple state and its
//! skipped-key stores, and at most one skipped key matching the header), the Braid epoch's room,
//! and one 32-byte draw in the random source. The theorem says nothing of a run that falls
//! outside them, and it is not a result about `Session::decrypt` as a whole. The proofs assume
//! only the four ceilings of `CounterHeadroom` (the clock, `events + 1 < u32::MAX`; the sparse
//! epoch, `+ 1 < u64::MAX`; the chain counters, `< u64::MAX`; the Braid epoch, `+ 1 < u64::MAX`).
//! This file checks all eleven bounds of `RetryRunBounds` and the Braid epoch: five of the
//! eleven follow from `Session::invariant` (checked here too), two more with the sparse epoch
//! ceiling, and one from the model; its checks are the only evidence on real runs about the four
//! assumed ceilings. This file drives a real establishment (the inputs of
//! `session-e2e.json`, `one-time-prekeys-first-message`, drawn through a stated-then-stream
//! random source) and a schedule of `decrypt` calls that reaches the outcomes listed below (and
//! not those listed as not reached), and at every call asserts the runtime form of what the record asks, read from the state the call
//! starts in. Those runs are the only evidence this file gives; no theorem is applied to them.
//!
//! # What is checked at every `decrypt` call
//!
//! * `Session::invariant` before and after;
//! * the random source is read as the model reads it (`Model.Lifecycle.decrypt`,
//!   `decryptRatchet`): **no draw** when the dispatch refuses (an initial frame that does not
//!   decode, or that is not a repeat of the one that established the session), when the terminal
//!   agreement guard refuses, when the ratchet frame does not decode, and when the incoming
//!   ratchet key is non-contributory; **exactly one 32-byte draw** from the first agreement
//!   onward, which is kept on every later refusal (a Triple refusal, an AEAD refusal) and on
//!   success. Nothing else is read: every call the source logs is a 32-byte fill;
//! * on a refusal the exported state is byte-equal to the state before; on a success it differs;
//! * the error is the expected one;
//! * the bounds below hold of the state before the call.
//!
//! # Premise to runtime check
//!
//! The state is read from `Session::export` (the layout of
//! `tacenta-spec/protocol/session-persistence.md`: the Session, Triple ratchet state, Ratchet
//! state, Sparse ratchet state and Braid sections). No library code is changed; the exported
//! `ns` and `nr` are checked against `public_state()` so a drift of the reader shows up.
//!
//! | Lean field | runtime check | read from |
//! |---|---|---|
//! | `classicalMatch` | skipped entries equal to the header's `(dh, n)`: at most 1 | ratchet state `skipped`, header of the frame (`decode_message`, inside `decode_initial` for a wrapper) |
//! | `classicalEvents` | `events + 1 < u32::MAX` | ratchet state `events` |
//! | `sparseEpoch` | `epoch + 1 < u64::MAX` | sparse state `epoch` |
//! | `sparseChainsRoom` | `chains + 2 < usize::MAX` (and below `2^32 - 1`) | sparse state `chains_count` |
//! | `sparseChainEpochs` | each chain epoch `+ 2 <= u64::MAX` | sparse state `chains` |
//! | `sparseSkippedEpochs` | each skipped epoch `+ 2 <= u64::MAX` | sparse state `skipped` |
//! | `sparseOutputEpoch` | `output.keyEpoch + 2 <= u64::MAX`; the output is not observable, but `step_receive` in `tacenta-core/braid/src/lib.rs` emits `Output { key_epoch: epoch, .. }` with the epoch the state held before the call. The bound is the same as `braidEpoch`'s (`epoch + 1 < u64::MAX` is `epoch <= u64::MAX - 2`), so it is checked by that row and has no check of its own | Braid blob epoch |
//! | `sparseMatch` | skipped entries equal to `(pq_epoch, pq_n)` of the header: at most 1 | sparse state `skipped` |
//! | `sparseCounters` | every present chain's `n < u64::MAX` | sparse state `chains` |
//! | `classicalStore` | `skipped + 2000 <= usize::MAX`, and `<= 2^32 - 1` whatever the width | ratchet state `skipped_count` |
//! | `sparseStore` | the same, for the sparse store | sparse state `skipped_count` |
//! | `braidEpoch` (run) | `epoch + 1 < u64::MAX`, for a Braid that has not failed | Braid blob epoch |
//! | `draw` (run) | the source offers a draw on demand (a stated draw, then a stream, never exhausted); the call is asserted to read the number the model fixes for its branch, never more than one | the counting source's log |
//!
//! **Not observable from outside, and so not checked:** `chunk` and `honest` (`IncomingChunkRefines`,
//! `HonestChunk`) say the incoming agreement chunk is a codeword of one erasure-code source that
//! fits the decoder it is fed to. A chunk carries no source, so no runtime check can ask it. The
//! frames this file delivers that the genuine peer built are honest by construction; the frames
//! it alters (a forged tag, a changed ephemeral, a zeroed ratchet key) are altered outside the
//! chunk, and no frame with a spliced chunk is delivered. The maximum of `ns`/`nr` is not a
//! premise. The Braid epoch's `keyEpoch` bound is a proxy, as the row says.
//!
//! # Negative controls
//!
//! `the_premise_checks_fail_on_states_outside_the_ceilings` mutates an observed state, one field
//! at a time, and shows that each of eight checks fails with the Lean field's name
//! (`classicalEvents`, `sparseEpoch`, `sparseChainEpochs`, `sparseCounters`,
//! `sparseSkippedEpochs`, `braidEpoch`, `classicalMatch`, `sparseMatch`; `braidEpoch` is also
//! the check of `sparseOutputEpoch`, which has the same bound). `the_room_checks_fail_at_their_boundaries`
//! calls the three length checks (`classicalStore`, `sparseStore`, `sparseChainsRoom`) with
//! lengths no session holds, at the boundary of `2^32 - 1` and of the machine's `usize::MAX`,
//! through the same function the call-time checks use; it tests the arithmetic, not a state
//! with billions of entries. `a_session_the_invariant_accepts_can_fall_outside_the_event_ceiling`
//! shows the one gap between `Session::invariant` and the premises that the documentation already
//! names: `events = u32::MAX - 1` imports, and is outside `classicalEvents`.
//!
//! # Outcomes reached (each in a test below)
//!
//! * (a) a ratchet frame passes through the dispatch and is accepted (the initiator reads the
//!   responder's reply);
//! * (b) a repeat of the initial message, in a torsion-equivalent spelling of the stored
//!   ephemeral, is accepted;
//! * (c) a repeat whose ephemeral is another valid key, and one whose ephemeral is low order, are
//!   refused as not a repeat;
//! * (d) a ratchet frame on an existing chain, a frame that skips and a late arrival of a skipped
//!   key (one stored key matches the header);
//! * (e) the replay of an accepted ratchet frame, bare and inside an initial wrapper, is refused;
//! * (f) a frame beyond `MAX_SKIP` is refused, and the one at the limit is accepted;
//! * (g) a forged tag, and a ciphertext shortened by a byte, are refused by the AEAD;
//! * (h) an unknown type byte and an unknown version byte are refused by the decoder;
//! * (i) a frame truncated inside its header, an empty frame, and a truncated initial wrapper are
//!   refused by the decoder;
//! * (j) an initial frame delivered to an initiator's session is refused as not a repeat;
//! * (k) a full skipped-key store: a forged frame evicts nothing, the genuine one is accepted
//!   after the oldest keys are evicted from a working copy;
//! * a ratchet frame whose ratchet key is low order (non-contributory incoming agreement), refused
//!   before the draw;
//! * the terminal agreement guard, on a session imported with a failed Braid.
//!
//! # Outcomes not reached
//!
//! * (l) a responder with no established ephemeral. The model does not separate (l) from (j):
//!   `Model.Lifecycle.repeatedInitial` reads only `establishedEphemeral`, so both are the same
//!   branch, and (j) reaches it. In the Rust `is_responder()` is defined as
//!   `established_ephemeral.is_some()`, so a responder without one does not exist by definition;
//!   `Session::import` refuses a hand-built one as `Inconsistent` (invariant clauses c and d), and
//!   `a_responder_without_an_established_ephemeral_cannot_be_imported` holds that refusal. That
//!   test shows one state is refused; the argument is the definition.
//! * the second agreement refusing (`candidate_key.agree(peer)` after the first succeeded): both
//!   agreements are against the same `peer`, and a clamped scalar yields all zero for a
//!   low-order point whichever the scalar is, so the first refusal is the only reachable one.
//! * the model's ceiling refusal for an exhausted source: it has no counterpart in Rust, and the
//!   source here is a stream.
//! * a sparse-only `TooManySkipped`, a switch between the two stores in the eviction loop, a
//!   second eviction round, a run whose frame names an epoch the state holds no chain for, and a
//!   sparse refusal other than the out-of-order key after an eviction (step "k: an evicted key"):
//!   not built here.
//!
//! The `ExactRng` shape (a stated draw schedule, with the length of each draw checked) is copied
//! from `tacenta-test-vectors/runners/rust/src/session_e2e.rs` rather than imported, with a log
//! of every call and a stream after the stated draws; the stream is splitmix64, written out here
//! so the bytes do not depend on a generator crate. The test is deterministic and does not
//! depend on the width of `usize`.

use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::montgomery::MontgomeryPoint;
use curve25519_dalek::traits::IsIdentity;
use rand_core::{CryptoRng, RngCore};
use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;
use tacenta_core::primitives::dh;
use tacenta_core::ratchet::{MAX_SKIP, MAX_SKIPPED_STORE, RatchetError};
use tacenta_core::serialization::{
    DecodeError, MessageType, VERSION, decode_initial, decode_message, message_type,
};
use tacenta_core::sessions::{
    Identity, LifecycleError, Session, SessionDecodeError, establish_initiator, establish_responder,
};
use tacenta_spqr::SpqrError;
use tacenta_triple::TripleError;

// ---------------------------------------------------------------------------------------------
// The random source
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum Call {
    Fill(usize),
    TryFill(usize),
    NextU32,
    NextU64,
}

/// A random source that logs every call, yields a list of stated draws first (each length
/// checked), then a deterministic stream, and counts the draws a caller is allowed.
struct Counting {
    log: Rc<RefCell<Vec<Call>>>,
    stated: VecDeque<Vec<u8>>,
    state: u64,
}

impl Counting {
    fn new(stated: Vec<Vec<u8>>, seed: u64) -> (Counting, Rc<RefCell<Vec<Call>>>) {
        let log = Rc::new(RefCell::new(Vec::new()));
        (
            Counting {
                log: log.clone(),
                stated: stated.into(),
                state: seed,
            },
            log,
        )
    }

    fn unused(&self) -> usize {
        self.stated.len()
    }

    fn stream(&mut self, dest: &mut [u8]) {
        for d in dest.iter_mut() {
            self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            *d = ((z ^ (z >> 31)) >> 24) as u8;
        }
    }
}

impl RngCore for Counting {
    fn next_u32(&mut self) -> u32 {
        self.log.borrow_mut().push(Call::NextU32);
        let mut b = [0u8; 4];
        self.stream(&mut b);
        u32::from_le_bytes(b)
    }
    fn next_u64(&mut self) -> u64 {
        self.log.borrow_mut().push(Call::NextU64);
        let mut b = [0u8; 8];
        self.stream(&mut b);
        u64::from_le_bytes(b)
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.log.borrow_mut().push(Call::Fill(dest.len()));
        match self.stated.pop_front() {
            Some(chunk) => {
                assert_eq!(
                    chunk.len(),
                    dest.len(),
                    "a stated draw of {} bytes was asked for {}",
                    chunk.len(),
                    dest.len()
                );
                dest.copy_from_slice(&chunk);
            }
            None => self.stream(dest),
        }
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.log.borrow_mut().push(Call::TryFill(dest.len()));
        self.stream(dest);
        Ok(())
    }
}
impl CryptoRng for Counting {}

fn seed_of(label: &str) -> u64 {
    // FNV-1a, so a step's stream is fixed by its name and independent of test order.
    let mut h = 0xcbf2_9ce4_8422_2325u64;
    for b in label.bytes() {
        h = (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// A stream with no stated draws, for the calls under no check (`encrypt`).
fn plain(label: &str) -> Counting {
    Counting::new(Vec::new(), seed_of(label)).0
}

// ---------------------------------------------------------------------------------------------
// Reading the state from the export
// ---------------------------------------------------------------------------------------------

fn be32(b: &[u8], at: usize) -> u32 {
    u32::from_be_bytes(b[at..at + 4].try_into().unwrap())
}

fn be64(b: &[u8], at: usize) -> u64 {
    u64::from_be_bytes(b[at..at + 8].try_into().unwrap())
}

struct PqChain {
    epoch: u64,
    send: Option<u64>,
    receive: Option<u64>,
}

struct Observed {
    ns: u32,
    nr: u32,
    events: u32,
    classical_skipped: Vec<([u8; 32], u32)>,
    pq_epoch: u64,
    pq_chains: Vec<PqChain>,
    pq_skipped: Vec<(u64, u64)>,
    braid_epoch: Option<u64>,
}

const BRAID_FAILED_TAG: u8 = 11;

/// The ratchet state's fixed part and one skipped entry (session-persistence.md, Ratchet state).
const CLASSICAL_FIXED: usize = 185;
const CLASSICAL_ENTRY: usize = 72;
/// The sparse state's fixed part, one chains entry and one skipped entry (Sparse ratchet state).
const PQ_FIXED: usize = 46;
const PQ_CHAIN: usize = 90;
const PQ_ENTRY: usize = 48;

fn observe(session: &Session) -> Observed {
    let bytes = session.export();
    let b: &[u8] = &bytes;
    assert_eq!(b[0], 0x01, "session version");
    let triple_len = be32(b, 1) as usize;
    let triple = &b[5..5 + triple_len];
    let braid_at = 5 + triple_len;
    let braid_len = be32(b, braid_at) as usize;
    let braid = &b[braid_at + 4..braid_at + 4 + braid_len];

    assert_eq!(triple[0], 0x01, "triple version");
    let classical_len = be32(triple, 1) as usize;
    let classical = &triple[5..5 + classical_len];
    let pq_at = 5 + classical_len;
    let pq_len = be32(triple, pq_at) as usize;
    let pq = &triple[pq_at + 4..pq_at + 4 + pq_len];
    assert_eq!(pq_at + 4 + pq_len, triple.len(), "triple state length");

    assert_eq!(classical[0], 0x01, "ratchet version");
    let count = be32(classical, 181) as usize;
    assert_eq!(
        classical.len(),
        CLASSICAL_FIXED + count * CLASSICAL_ENTRY,
        "ratchet state length"
    );
    let classical_skipped = (0..count)
        .map(|i| {
            let at = CLASSICAL_FIXED + i * CLASSICAL_ENTRY;
            let mut dh = [0u8; 32];
            dh.copy_from_slice(&classical[at..at + 32]);
            (dh, be32(classical, at + 32))
        })
        .collect();

    assert_eq!(pq[0], 0x01, "sparse version");
    let chains_count = be32(pq, 42) as usize;
    let pq_chains: Vec<PqChain> = (0..chains_count)
        .map(|i| {
            let at = PQ_FIXED + i * PQ_CHAIN;
            let chain = |at: usize| (pq[at] == 1).then(|| be64(pq, at + 33));
            PqChain {
                epoch: be64(pq, at),
                send: chain(at + 8),
                receive: chain(at + 49),
            }
        })
        .collect();
    let skipped_at = PQ_FIXED + chains_count * PQ_CHAIN;
    let skipped_count = be32(pq, skipped_at) as usize;
    assert_eq!(
        pq.len(),
        skipped_at + 4 + skipped_count * PQ_ENTRY,
        "sparse state length"
    );
    let pq_skipped = (0..skipped_count)
        .map(|i| {
            let at = skipped_at + 4 + i * PQ_ENTRY;
            (be64(pq, at), be64(pq, at + 8))
        })
        .collect();

    let braid_tag = braid[1];
    let braid_epoch = (braid_tag != BRAID_FAILED_TAG).then(|| be64(braid, 2));

    let observed = Observed {
        ns: be32(classical, 164),
        nr: be32(classical, 168),
        events: be32(classical, 176),
        classical_skipped,
        pq_epoch: be64(pq, 33),
        pq_chains,
        pq_skipped,
        braid_epoch,
    };
    // The reader against the public counters, so a layout drift cannot pass silently.
    let public = session.public_state();
    assert_eq!(observed.ns, public.sent, "reader: ns");
    assert_eq!(observed.nr, public.received, "reader: nr");
    observed
}

/// The header fields the premises name.
struct Header {
    dh: [u8; 32],
    n: u32,
    pq_epoch: u64,
    pq_n: u64,
}

/// The header of the ratchet frame the call would hand to `decrypt_ratchet`: the frame itself, or
/// the one inside an initial wrapper. `None` for a frame that does not decode, where the run
/// record says nothing of the header.
fn header_of(message: &[u8]) -> Option<Header> {
    let inner = match message_type(message) {
        Some(MessageType::Initial) => decode_initial(message).ok()?.message,
        _ => message.to_vec(),
    };
    let decoded = decode_message(&inner).ok()?;
    Some(Header {
        dh: decoded.header.dh,
        n: decoded.header.n,
        pq_epoch: decoded.header.pq_epoch,
        pq_n: decoded.header.pq_n,
    })
}

const CMAX32: u64 = u32::MAX as u64;
/// `epochsKept` of `Model.SparseRatchet`.
const EPOCHS_KEPT: u64 = 2;

/// What a call's premises looked at, so a test can show that a check was not vacuous.
#[derive(Default, Debug)]
struct Premises {
    header_decoded: bool,
    classical_matches: usize,
    sparse_matches: usize,
    classical_skipped: usize,
    sparse_skipped: usize,
}

/// `RetryRunBounds` and the state-side fields of `DecryptRatchetRun`, of the state before a call.
fn check_premises(label: &str, o: &Observed, header: Option<&Header>) -> Premises {
    let mut p = Premises {
        classical_skipped: o.classical_skipped.len(),
        sparse_skipped: o.pq_skipped.len(),
        ..Premises::default()
    };
    if let Some(h) = header {
        p.header_decoded = true;
        p.classical_matches = o
            .classical_skipped
            .iter()
            .filter(|(dh, n)| *dh == h.dh && *n == h.n)
            .count();
        p.sparse_matches = o
            .pq_skipped
            .iter()
            .filter(|(e, n)| *e == h.pq_epoch && *n == h.pq_n)
            .count();
        assert!(
            p.classical_matches <= 1,
            "{label}: classicalMatch: {} stored keys match the header",
            p.classical_matches
        );
        assert!(
            p.sparse_matches <= 1,
            "{label}: sparseMatch: {} stored keys match the header",
            p.sparse_matches
        );
    }
    assert!(
        u64::from(o.events) + 1 < CMAX32,
        "{label}: classicalEvents: events {}",
        o.events
    );
    assert!(
        o.pq_epoch < u64::MAX - 1,
        "{label}: sparseEpoch: epoch {}",
        o.pq_epoch
    );
    check_room(
        label,
        o.classical_skipped.len(),
        o.pq_skipped.len(),
        o.pq_chains.len(),
    );
    for c in &o.pq_chains {
        assert!(
            c.epoch <= u64::MAX - EPOCHS_KEPT,
            "{label}: sparseChainEpochs: chain epoch {}",
            c.epoch
        );
        for n in [c.send, c.receive].into_iter().flatten() {
            assert!(n < u64::MAX, "{label}: sparseCounters: chain counter {n}");
        }
    }
    for (e, _) in &o.pq_skipped {
        assert!(
            *e <= u64::MAX - EPOCHS_KEPT,
            "{label}: sparseSkippedEpochs: skipped epoch {e}"
        );
    }
    // `sparseOutputEpoch` is this same bound (the Braid's `step_receive` emits the epoch it held),
    // so this assertion is its check as well; a failed Braid has no epoch and no output.
    if let Some(epoch) = o.braid_epoch {
        assert!(
            epoch + 1 < u64::MAX,
            "{label}: braidEpoch (and sparseOutputEpoch): Braid epoch {epoch}"
        );
    }
    p
}

/// `store + cap <= cMax Usize`, for `cMax Usize` at the width of the machine and at 32 bits.
fn store_room(len: usize, cap: usize) -> bool {
    (len as u128) + (cap as u128) <= usize::MAX as u128
        && (len as u128) + (cap as u128) <= CMAX32 as u128
}

/// `chains + 2 < Usize.max`, at the width of the machine and at 32 bits.
fn chains_room(len: usize) -> bool {
    (len as u128) + 2 < usize::MAX as u128 && (len as u128) + 2 < CMAX32 as u128
}

/// The three bounds that depend only on a length, so a control can call them with a length no
/// session holds.
fn check_room(label: &str, classical_store: usize, sparse_store: usize, chains: usize) {
    assert!(
        chains_room(chains),
        "{label}: sparseChainsRoom: {chains} chains"
    );
    assert!(
        store_room(classical_store, MAX_SKIPPED_STORE),
        "{label}: classicalStore: {classical_store} stored keys"
    );
    assert!(
        store_room(sparse_store, tacenta_spqr::MAX_SKIPPED_STORE),
        "{label}: sparseStore: {sparse_store} stored keys"
    );
}

// ---------------------------------------------------------------------------------------------
// One checked call
// ---------------------------------------------------------------------------------------------

enum Expect {
    Plaintext(Vec<u8>),
    Refused(fn(&LifecycleError) -> bool),
}

struct Step<'a> {
    label: &'a str,
    stated: Vec<Vec<u8>>,
    /// The number of 32-byte fills the model reads on this branch: 0 or 1.
    draws: usize,
    expect: Expect,
}

impl<'a> Step<'a> {
    fn ok(label: &'a str, plaintext: &[u8]) -> Step<'a> {
        Step {
            label,
            stated: Vec::new(),
            draws: 1,
            expect: Expect::Plaintext(plaintext.to_vec()),
        }
    }
    /// Refused after the draw (a Triple refusal, an AEAD refusal): the draw is kept.
    fn refused_after_draw(label: &'a str, is: fn(&LifecycleError) -> bool) -> Step<'a> {
        Step {
            label,
            stated: Vec::new(),
            draws: 1,
            expect: Expect::Refused(is),
        }
    }
    /// Refused before the draw (dispatch, guard, decode, non-contributory key).
    fn refused_before_draw(label: &'a str, is: fn(&LifecycleError) -> bool) -> Step<'a> {
        Step {
            label,
            stated: Vec::new(),
            draws: 0,
            expect: Expect::Refused(is),
        }
    }
}

fn is_not_a_repeat(e: &LifecycleError) -> bool {
    matches!(e, LifecycleError::NotARepeatedInitial)
}
fn is_aead(e: &LifecycleError) -> bool {
    matches!(e, LifecycleError::Aead)
}
/// A replay is refused by the classical half, as an out-of-order message. Neither full-store
/// refusal may reach the caller (the eviction loop makes room or reports the other reason), so
/// the reason is pinned and not only the variant.
fn is_classical_out_of_order(e: &LifecycleError) -> bool {
    matches!(
        e,
        LifecycleError::Triple(TripleError::Classical(RatchetError::OutOfOrder))
    )
}
fn is_sparse_out_of_order(e: &LifecycleError) -> bool {
    matches!(
        e,
        LifecycleError::Triple(TripleError::PostQuantum(SpqrError::OutOfOrder))
    )
}
fn is_too_short(e: &LifecycleError) -> bool {
    matches!(e, LifecycleError::Decode(DecodeError::TooShort))
}

/// `Session::decrypt` with every check of the module documentation around it.
fn checked(
    session: &mut Session,
    message: &[u8],
    step: Step<'_>,
) -> (Result<Vec<u8>, LifecycleError>, Premises) {
    let label = step.label;
    assert!(session.invariant(), "{label}: invariant before");
    let before = session.export().to_vec();
    let observed = observe(session);
    let header = header_of(message);
    let premises = check_premises(label, &observed, header.as_ref());

    let stated = step.stated.len();
    let (mut rng, log) = Counting::new(step.stated, seed_of(label));
    let result = session.decrypt(message, &mut rng);

    assert!(session.invariant(), "{label}: invariant after");
    let calls = log.borrow().clone();
    let fills = calls.iter().filter(|c| **c == Call::Fill(32)).count();
    assert_eq!(
        calls.len(),
        fills,
        "{label}: a call other than a 32-byte fill: {calls:?}"
    );
    assert_eq!(
        fills, step.draws,
        "{label}: the model reads {} draw(s) on this branch, the run read {fills}",
        step.draws
    );
    assert_eq!(
        rng.unused(),
        stated.saturating_sub(fills),
        "{label}: stated draws"
    );

    let after = session.export().to_vec();
    match (&result, step.expect) {
        (Ok(plaintext), Expect::Plaintext(want)) => {
            assert_eq!(*plaintext, want, "{label}: plaintext");
            assert_ne!(after, before, "{label}: an accepted call changes the state");
        }
        (Err(error), Expect::Refused(is)) => {
            assert!(is(error), "{label}: unexpected refusal {error:?}");
            assert_eq!(after, before, "{label}: a refusal changes the state");
        }
        (got, _) => panic!("{label}: wrong outcome {got:?}"),
    }
    println!(
        "{label}: draws={fills} outcome={:?} header={} classical_matches={} sparse_matches={} \
         classical_skipped={} sparse_skipped={}",
        result.as_ref().map(|p| p.len()),
        premises.header_decoded,
        premises.classical_matches,
        premises.sparse_matches,
        premises.classical_skipped,
        premises.sparse_skipped,
    );
    (result, premises)
}

// ---------------------------------------------------------------------------------------------
// Establishment from the end-to-end vector
// ---------------------------------------------------------------------------------------------

const VECTOR: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../tacenta-test-vectors/vectors/session-establishment/session-e2e.json"
);

struct Vector(serde_json::Value);

impl Vector {
    fn load() -> Vector {
        let text = std::fs::read_to_string(VECTOR).expect("the end-to-end vector file");
        let all: serde_json::Value = serde_json::from_str(&text).unwrap();
        let first = all["vectors"][0].clone();
        assert_eq!(first["id"], "one-time-prekeys-first-message");
        Vector(first)
    }
    fn hex(&self, section: &str, name: &str) -> Vec<u8> {
        hex::decode(self.0[section][name].as_str().expect(name)).expect(name)
    }
    fn input(&self, name: &str) -> Vec<u8> {
        self.hex("inputs", name)
    }
    fn field(&self, name: &str) -> Vec<u8> {
        self.hex("fields", name)
    }
    fn draws(&self, names: &[&str]) -> Vec<Vec<u8>> {
        names.iter().map(|n| self.input(n)).collect()
    }
}

fn array32(bytes: &[u8]) -> [u8; 32] {
    bytes.try_into().expect("32 bytes")
}

/// The seven other canonical u-coordinates in the agreement class of a curve point, sorted
/// (copied from the vector runner).
fn torsion_spellings(ephemeral: [u8; 32]) -> Vec<[u8; 32]> {
    let torsion_bytes = array32(
        &hex::decode("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a").unwrap(),
    );
    let torsion: EdwardsPoint = CompressedEdwardsY(torsion_bytes).decompress().unwrap();
    assert!(torsion.is_small_order());
    assert!(!(torsion + torsion + torsion + torsion).is_identity());
    let point = MontgomeryPoint(ephemeral).to_edwards(0).unwrap();
    let mut out = Vec::new();
    let mut multiple = torsion;
    for _ in 1..8 {
        let spelling = (point + multiple).to_montgomery().to_bytes();
        assert_ne!(spelling, ephemeral);
        assert!(spelling[31] < 0x80);
        out.push(spelling);
        multiple += torsion;
    }
    out.sort();
    out.dedup();
    assert_eq!(out.len(), 7);
    out
}

/// An initial message is `version || type || EncodeEC(identity) || EncodeEC(ephemeral) || ...`.
const EPHEMERAL_KEY: core::ops::Range<usize> = 36..68;

fn replace_ephemeral(message: &[u8], key: [u8; 32]) -> Vec<u8> {
    let mut out = message.to_vec();
    out[EPHEMERAL_KEY].copy_from_slice(&key);
    out
}

struct Established {
    alice: Session,
    bob: Session,
    /// Alice's first and second initial messages (the second is a repeat around a new ratchet
    /// message).
    initial: Vec<u8>,
    repeat: Vec<u8>,
    repeat_plaintext: Vec<u8>,
    /// The loaded vector, for the draws and recorded bytes later steps state.
    vector: Vector,
}

/// The one-time-prekeys flow of `session-e2e.json`: every draw named in the vector is stated and
/// its length checked, and the responder is established from a torsion-spelled copy of the first
/// message, as the vector does. The sessions are compared with the vector's recorded bytes.
fn establish() -> Established {
    let v = Vector::load();
    let alice = Identity::from_secret(array32(&v.input("alice_identity_secret")));
    let bob = Identity::from_secret(array32(&v.input("bob_identity_secret")));
    let plaintext = v.input("plaintext");
    let repeat_plaintext = v.input("repeat_plaintext");

    let prekey_draws = v.draws(&[
        "bob_signed_prekey_secret",
        "bob_signed_prekey_signature_nonce",
        "bob_one_time_curve_secret",
        "bob_last_resort_kem_d_z",
        "bob_last_resort_kem_signature_nonce",
        "bob_one_time_kem_d_z",
        "bob_one_time_kem_signature_nonce",
    ]);
    let (mut rng, log) = Counting::new(prekey_draws, 0);
    let mut store = bob.create_prekeys(1, &mut rng);
    assert_eq!(rng.unused(), 0);
    assert_eq!(log.borrow().len(), 7);
    let published = store.publish();

    let (mut rng, log) = Counting::new(
        v.draws(&[
            "alice_ephemeral_secret",
            "alice_kem_encapsulation_m",
            "alice_ratchet_secret",
        ]),
        0,
    );
    let mut alice_session = establish_initiator(&alice, &published, &mut rng).unwrap();
    assert_eq!((rng.unused(), log.borrow().len()), (0, 3));

    let (mut rng, log) = Counting::new(v.draws(&["alice_braid_keygen_d_z"]), 0);
    let initial = alice_session.encrypt(&plaintext, &mut rng).unwrap();
    assert_eq!((rng.unused(), log.borrow().len()), (0, 1));
    assert_eq!(
        alice_session.export().to_vec(),
        v.field("alice_session_after_first_send")
    );
    assert_eq!(initial, v.field("initial_message"));

    let (mut rng, log) = Counting::new(Vec::new(), 0);
    let repeat = alice_session.encrypt(&repeat_plaintext, &mut rng).unwrap();
    assert!(log.borrow().is_empty(), "a repeated initial draws nothing");
    assert_eq!(repeat, v.field("repeat_initial"));

    // The responder is established from the torsion-spelled copy, so its stored ephemeral is not
    // the spelling the initiator's repeats carry.
    let mut ephemeral = [0u8; 32];
    ephemeral.copy_from_slice(&initial[EPHEMERAL_KEY]);
    let torsion_initial = replace_ephemeral(&initial, torsion_spellings(ephemeral)[0]);
    assert_eq!(torsion_initial, v.field("torsion_initial"));
    let (mut rng, log) = Counting::new(v.draws(&["bob_ratchet_secret"]), 0);
    let (bob_session, recovered) =
        establish_responder(&bob, &mut store, &torsion_initial, &mut rng).unwrap();
    assert_eq!((rng.unused(), log.borrow().len()), (0, 1));
    assert_eq!(recovered, plaintext);
    assert_eq!(
        bob_session.export().to_vec(),
        v.field("bob_session_after_receipt")
    );
    assert!(alice_session.invariant() && bob_session.invariant());

    Established {
        alice: alice_session,
        bob: bob_session,
        initial,
        repeat,
        repeat_plaintext,
        vector: v,
    }
}

/// The responder reads the repeat, then answers once, so the initiator stops wrapping. Returns the
/// pair. Reading the repeat keeps the two sparse counters level (the initiator has sent two
/// messages, and the responder has read two), which the skip-limit tests below count from.
fn answered_pair() -> (Session, Session) {
    let Established {
        alice,
        bob,
        repeat,
        repeat_plaintext,
        vector,
        ..
    } = establish();
    let (mut alice, mut bob) = (alice, bob);
    let (r, _) = checked(
        &mut bob,
        &repeat,
        Step {
            stated: vector.draws(&["bob_repeat_random"]),
            ..Step::ok("answered: bob reads the repeat", &repeat_plaintext)
        },
    );
    assert!(r.is_ok());
    let reply = bob
        .encrypt(b"answer", &mut plain("answered:reply"))
        .unwrap();
    let (result, _) = checked(
        &mut alice,
        &reply,
        Step::ok("answered: alice reads the answer", b"answer"),
    );
    assert!(result.is_ok());
    (alice, bob)
}

fn forge(message: &[u8]) -> Vec<u8> {
    let mut m = message.to_vec();
    let last = m.len() - 1;
    m[last] ^= 0x01;
    m
}

// ---------------------------------------------------------------------------------------------
// The schedule
// ---------------------------------------------------------------------------------------------

/// Outcomes (a) to (e), (g) to (j) and the non-contributory refusal, on one pair, in order.
#[test]
fn every_outcome_of_the_schedule_meets_the_premises() {
    let Established {
        mut alice,
        mut bob,
        initial,
        repeat,
        repeat_plaintext,
        vector,
    } = establish();

    // (c) A repeat whose ephemeral is low order, and one whose ephemeral is another valid key,
    // are refused as not a repeat. Dispatch refusals: no draw.
    let (r, _) = checked(
        &mut bob,
        &replace_ephemeral(&repeat, [0u8; 32]),
        Step::refused_before_draw("c: low-order ephemeral", is_not_a_repeat),
    );
    assert!(r.is_err());
    let other = *dh::PrivateKey::from_bytes([7u8; 32])
        .public_key()
        .as_bytes();
    let (r, _) = checked(
        &mut bob,
        &replace_ephemeral(&repeat, other),
        Step::refused_before_draw("c: another valid ephemeral", is_not_a_repeat),
    );
    assert!(r.is_err());

    // (e) The first initial message again, canonical this time: the stored ephemeral is its
    // torsion-spelled twin, so the wrapper is recognised, and the ratchet message inside has
    // been read. The refusal comes after the draw.
    let (r, _) = checked(
        &mut bob,
        &initial,
        Step::refused_after_draw(
            "e: replay inside a recognised wrapper",
            is_classical_out_of_order,
        ),
    );
    assert!(r.is_err());

    // (b) The repeat is accepted, and the state is the vector's.
    let (r, _) = checked(
        &mut bob,
        &repeat,
        Step {
            stated: vector.draws(&["bob_repeat_random"]),
            ..Step::ok("b: accepted repeat", &repeat_plaintext)
        },
    );
    assert!(r.is_ok());
    assert_eq!(
        bob.export().to_vec(),
        vector.field("bob_session_after_repeat")
    );

    // (j) An initial message delivered to an initiator: it holds no established ephemeral.
    let (r, _) = checked(
        &mut alice,
        &repeat,
        Step::refused_before_draw("j: initial message to an initiator", is_not_a_repeat),
    );
    assert!(r.is_err());

    // (a) The responder answers; the ratchet frame passes through the dispatch on the
    // initiator, which takes a Diffie-Hellman step.
    let reply = bob.encrypt(b"r1", &mut plain("a:reply")).unwrap();
    let (r, _) = checked(
        &mut alice,
        &reply,
        Step::ok("a: pass-through success", b"r1"),
    );
    assert!(r.is_ok());

    // (d) On Alice's new chain: the first message steps Bob's ratchet, the second is on the
    // chain that step opened.
    let sent: Vec<Vec<u8>> = (0..5)
        .map(|i| {
            alice
                .encrypt(
                    format!("a{i}").as_bytes(),
                    &mut plain(&format!("d:send{i}")),
                )
                .unwrap()
        })
        .collect();
    for (i, expected) in [(0usize, "a0"), (1, "a1")] {
        let (r, _) = checked(
            &mut bob,
            &sent[i],
            Step::ok(["d: step", "d: existing chain"][i], expected.as_bytes()),
        );
        assert!(r.is_ok());
    }
    // A message that skips two: a4 before a3 and a2. Two keys are stored in each store.
    let (r, _) = checked(&mut bob, &sent[4], Step::ok("d: skip two", b"a4"));
    assert!(r.is_ok());
    assert_eq!(observe(&bob).classical_skipped.len(), 2);
    assert_eq!(observe(&bob).pq_skipped.len(), 2);
    // The late arrival of a skipped key: one stored key matches the header in each store, so
    // the "at most one" bound is met with equality, not vacuously.
    let (r, premises) = checked(&mut bob, &sent[2], Step::ok("d: late skipped key", b"a2"));
    assert!(r.is_ok());
    assert_eq!(premises.classical_matches, 1, "classicalMatch was vacuous");
    assert_eq!(premises.sparse_matches, 1, "sparseMatch was vacuous");

    // (e) The replay of an accepted ratchet frame, and of a skipped key already used.
    for (i, label) in [
        (1usize, "e: replay of an accepted frame"),
        (2, "e: replay of a used skipped key"),
    ] {
        let (r, premises) = checked(
            &mut bob,
            &sent[i],
            Step::refused_after_draw(label, is_classical_out_of_order),
        );
        assert!(r.is_err());
        assert_eq!(premises.classical_matches, 0);
    }

    // (g) A forged tag: refused by the AEAD after the draw, and the genuine frame still
    // arrives. A ciphertext one byte short fails the same way.
    let (r, _) = checked(
        &mut bob,
        &forge(&sent[3]),
        Step::refused_after_draw("g: forged tag", is_aead),
    );
    assert!(r.is_err());
    let shorter = &sent[3][..sent[3].len() - 1];
    let (r, _) = checked(
        &mut bob,
        shorter,
        Step::refused_after_draw("g: ciphertext one byte short", is_aead),
    );
    assert!(r.is_err());
    let (r, _) = checked(
        &mut bob,
        &sent[3],
        Step::ok("g: the genuine frame after forgeries", b"a3"),
    );
    assert!(r.is_ok());

    // (h) An unknown type byte and an unknown version byte pass the dispatch and are refused by
    // the ratchet decoder.
    let mut unknown_type = sent[3].clone();
    unknown_type[1] = 0x7f;
    let (r, _) = checked(
        &mut bob,
        &unknown_type,
        Step::refused_before_draw("h: unknown type byte", |e| {
            matches!(e, LifecycleError::Decode(DecodeError::WrongType))
        }),
    );
    assert!(r.is_err());
    let mut unknown_version = sent[3].clone();
    unknown_version[0] = VERSION.wrapping_add(1);
    let (r, _) = checked(
        &mut bob,
        &unknown_version,
        Step::refused_before_draw("h: unknown version byte", |e| {
            matches!(e, LifecycleError::Decode(DecodeError::UnknownVersion))
        }),
    );
    assert!(r.is_err());

    // (i) Truncation: inside the header, an empty frame, and an initial wrapper cut short (a
    // dispatch decode refusal).
    let (r, _) = checked(
        &mut bob,
        &sent[3][..40],
        Step::refused_before_draw("i: truncated inside the header", is_too_short),
    );
    assert!(r.is_err());
    let (r, _) = checked(
        &mut bob,
        &[],
        Step::refused_before_draw("i: empty frame", is_too_short),
    );
    assert!(r.is_err());
    let (r, _) = checked(
        &mut bob,
        &repeat[..60],
        Step::refused_before_draw("i: truncated initial wrapper", is_too_short),
    );
    assert!(r.is_err());

    // A ratchet frame whose ratchet key is low order: the incoming agreement is refused, before
    // the draw.
    let mut zero_key = sent[3].clone();
    zero_key[2..34].fill(0);
    let (r, _) = checked(
        &mut bob,
        &zero_key,
        Step::refused_before_draw("non-contributory ratchet key", |e| {
            matches!(
                e,
                LifecycleError::Handshake(
                    tacenta_core::sessions::SessionError::NonContributoryAgreement
                )
            )
        }),
    );
    assert!(r.is_err());

    // The conversation goes on after all of it.
    let more = alice.encrypt(b"after", &mut plain("tail:send")).unwrap();
    let (r, _) = checked(
        &mut bob,
        &more,
        Step::ok("tail: the session is alive", b"after"),
    );
    assert!(r.is_ok());
}

/// (f) The skip limit. A frame `MAX_SKIP + 1` ahead on a chain is refused after the draw and
/// changes nothing; the frame exactly `MAX_SKIP` ahead is accepted.
#[test]
fn a_frame_beyond_the_skip_limit_is_refused_and_the_limit_is_accepted() {
    let (mut alice, mut bob) = answered_pair();
    let sent: Vec<Vec<u8>> = (0..=MAX_SKIP + 1)
        .map(|i| {
            alice
                .encrypt(
                    format!("m{i}").as_bytes(),
                    &mut plain(&format!("f:send{i}")),
                )
                .unwrap()
        })
        .collect();
    let (r, _) = checked(
        &mut bob,
        &sent[MAX_SKIP as usize + 1],
        Step::refused_after_draw("f: beyond the skip limit", |e| {
            matches!(
                e,
                LifecycleError::Triple(TripleError::Classical(RatchetError::TooManySkipped))
            )
        }),
    );
    assert!(r.is_err());
    let (r, _) = checked(
        &mut bob,
        &sent[MAX_SKIP as usize],
        Step::ok(
            "f: exactly at the skip limit",
            format!("m{MAX_SKIP}").as_bytes(),
        ),
    );
    assert!(r.is_ok());
    assert_eq!(observe(&bob).classical_skipped.len(), MAX_SKIP as usize);
    // The next call starts from a store of MAX_SKIP keys and still meets the bounds; one of
    // the stored keys is the one this frame needs.
    let (r, premises) = checked(
        &mut bob,
        &sent[7],
        Step::ok("f: a stored key after the limit", b"m7"),
    );
    assert!(r.is_ok());
    assert_eq!(premises.classical_matches, 1);
}

/// One round of `store_eviction.rs`: Alice sends `MAX_SKIP + 1` messages on a fresh chain, Bob
/// receives only the last (storing `MAX_SKIP` keys in each store) and answers, so that the next
/// round starts a new chain. Returns Alice's undelivered messages.
fn round(alice: &mut Session, bob: &mut Session, label: &str) -> Vec<Vec<u8>> {
    let mut sent: Vec<Vec<u8>> = (0..=MAX_SKIP)
        .map(|i| {
            alice
                .encrypt(
                    format!("{label} {i}").as_bytes(),
                    &mut plain(&format!("{label}:send{i}")),
                )
                .unwrap()
        })
        .collect();
    let last = sent.pop().unwrap();
    let want = format!("{label} {MAX_SKIP}");
    let (r, _) = checked(
        bob,
        &last,
        Step::ok(&format!("{label}: last of the round"), want.as_bytes()),
    );
    assert!(r.is_ok());
    let ack = bob
        .encrypt(b"ack", &mut plain(&format!("{label}:ack")))
        .unwrap();
    let (r, _) = checked(alice, &ack, Step::ok(&format!("{label}: ack"), b"ack"));
    assert!(r.is_ok());
    sent
}

/// (k) A full skipped-key store. The third round's frame needs room: a forged copy of it is
/// refused after the draw and evicts nothing; the genuine one is accepted, and the oldest keys
/// go from a working copy.
#[test]
fn a_full_skipped_key_store_makes_room_and_a_forgery_evicts_nothing() {
    let (mut alice, mut bob) = answered_pair();
    let first = round(&mut alice, &mut bob, "one");
    let second = round(&mut alice, &mut bob, "two");
    let full = observe(&bob);
    assert_eq!(full.classical_skipped.len(), MAX_SKIPPED_STORE);
    assert_eq!(full.pq_skipped.len(), tacenta_spqr::MAX_SKIPPED_STORE);

    let mut third: Vec<Vec<u8>> = (0..=MAX_SKIP)
        .map(|i| {
            alice
                .encrypt(
                    format!("three {i}").as_bytes(),
                    &mut plain(&format!("k:send{i}")),
                )
                .unwrap()
        })
        .collect();
    let genuine = third.pop().unwrap();
    let (r, premises) = checked(
        &mut bob,
        &forge(&genuine),
        Step::refused_after_draw("k: forgery against a full store", is_aead),
    );
    assert!(r.is_err());
    assert_eq!(premises.classical_skipped, MAX_SKIPPED_STORE);
    assert_eq!(premises.sparse_skipped, tacenta_spqr::MAX_SKIPPED_STORE);

    // The forgery evicted nothing: the oldest key still opens its frame.
    let (r, _) = checked(
        &mut bob,
        &first[0],
        Step::ok("k: oldest key after the forgery", b"one 0"),
    );
    assert!(r.is_ok());

    let (r, premises) = checked(
        &mut bob,
        &genuine,
        Step::ok("k: store eviction", format!("three {MAX_SKIP}").as_bytes()),
    );
    assert!(r.is_ok());
    // That the eviction loop ran is shown by the evicted-key refusal below (`store_eviction.rs`
    // pins what it evicts); the premises of this call are those of a store at its cap.
    assert_eq!(premises.classical_skipped, MAX_SKIPPED_STORE - 1);
    let after = observe(&bob);
    assert!(after.classical_skipped.len() <= MAX_SKIPPED_STORE);
    assert!(after.pq_skipped.len() <= tacenta_spqr::MAX_SKIPPED_STORE);

    // Eviction is oldest first: the newest keys of round two remain, one of round one's does not.
    let (r, _) = checked(
        &mut bob,
        &second[MAX_SKIP as usize - 1],
        Step::ok("k: newest of round two", b"two 999"),
    );
    assert!(r.is_ok());
    let (r, _) = checked(
        &mut bob,
        &first[MAX_SKIP as usize / 2],
        Step::refused_after_draw("k: an evicted key", is_sparse_out_of_order),
    );
    assert!(r.is_err());
}

// ---------------------------------------------------------------------------------------------
// Sessions built by import
// ---------------------------------------------------------------------------------------------

/// (l) The session with no established ephemeral that `Session::invariant` accepts is an
/// initiator; a responder with its ephemeral removed is not importable.
#[test]
fn a_responder_without_an_established_ephemeral_cannot_be_imported() {
    let Established { bob, .. } = establish();
    let mut bytes = bob.export().to_vec();
    // The last field: presence(1) || len(4) || EncodeEC(33). Clear it.
    let cut = bytes.len() - (1 + 4 + 33);
    assert_eq!(bytes[cut], 0x01);
    bytes.truncate(cut);
    bytes.push(0x00);
    match Session::import(&bytes) {
        Err(SessionDecodeError::Inconsistent) => {}
        other => panic!("expected Inconsistent, got {:?}", other.map(|_| ())),
    }
}

/// The terminal agreement guard: a session imported with a failed Braid refuses everything, with
/// no draw and no change.
#[test]
fn a_session_with_a_failed_braid_refuses_before_the_draw() {
    let (mut alice, bob) = answered_pair();
    let bytes = bob.export().to_vec();
    let triple_len = be32(&bytes, 1) as usize;
    let braid_at = 5 + triple_len;
    let braid_len = be32(&bytes, braid_at) as usize;
    let version = bytes[braid_at + 4];
    let mut patched = bytes[..braid_at].to_vec();
    patched.extend_from_slice(&2u32.to_be_bytes());
    patched.extend_from_slice(&[version, BRAID_FAILED_TAG]);
    patched.extend_from_slice(&bytes[braid_at + 4 + braid_len..]);
    let mut failed = Session::import(&patched).expect("a failed Braid is a state the format has");
    assert!(failed.agreement_failed());

    let frame = alice
        .encrypt(b"into the void", &mut plain("failed:send"))
        .unwrap();
    // The guard comes before the decoder (`Model.Lifecycle.decryptRatchet`): a frame that would
    // not decode is refused as a failed agreement too, so swapping the two is caught here.
    for (label, message) in [
        ("terminal agreement guard", &frame[..]),
        ("terminal agreement guard, truncated frame", &frame[..40]),
        ("terminal agreement guard, empty frame", &[][..]),
    ] {
        let (r, _) = checked(
            &mut failed,
            message,
            Step::refused_before_draw(label, |e| matches!(e, LifecycleError::AgreementFailed)),
        );
        assert!(r.is_err());
    }
}

// ---------------------------------------------------------------------------------------------
// Negative controls: the checks can fail
// ---------------------------------------------------------------------------------------------

/// Run the premise checks on a mutated copy of an observed state and return the panic message.
fn refusal_of(mutate: impl FnOnce(&mut Observed, &mut Header)) -> String {
    let (_, mut bob) = answered_pair();
    let m = bob.encrypt(b"x", &mut plain("neg:send")).unwrap();
    let mut observed = observe(&bob);
    let mut header = header_of(&m).unwrap();
    // The state is in range before the mutation.
    check_premises("neg: baseline", &observed, Some(&header));
    mutate(&mut observed, &mut header);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_premises("neg", &observed, Some(&header))
    }));
    match result {
        Ok(_) => String::new(),
        Err(payload) => payload
            .downcast_ref::<String>()
            .cloned()
            .unwrap_or_default(),
    }
}

#[test]
fn the_premise_checks_fail_on_states_outside_the_ceilings() {
    let expect = |field: &str, message: String| {
        assert!(
            message.contains(field),
            "expected a {field} failure, got {message:?}"
        );
    };
    expect(
        "classicalEvents",
        refusal_of(|o, _| o.events = u32::MAX - 1),
    );
    expect("sparseEpoch", refusal_of(|o, _| o.pq_epoch = u64::MAX - 1));
    expect(
        "sparseChainEpochs",
        refusal_of(|o, _| o.pq_chains[0].epoch = u64::MAX - 1),
    );
    expect(
        "sparseCounters",
        refusal_of(|o, _| o.pq_chains[0].send = Some(u64::MAX)),
    );
    expect(
        "sparseSkippedEpochs",
        refusal_of(|o, _| o.pq_skipped.push((u64::MAX, 1))),
    );
    expect(
        "braidEpoch",
        refusal_of(|o, _| o.braid_epoch = Some(u64::MAX - 1)),
    );
    expect(
        "classicalMatch",
        refusal_of(|o, h| o.classical_skipped = vec![(h.dh, h.n); 2]),
    );
    expect(
        "sparseMatch",
        refusal_of(|o, h| o.pq_skipped = vec![(h.pq_epoch, h.pq_n); 2]),
    );
}

#[test]
fn the_room_checks_fail_at_their_boundaries() {
    let cap = MAX_SKIPPED_STORE;
    let sparse_cap = tacenta_spqr::MAX_SKIPPED_STORE;
    let top = CMAX32 as usize;
    // The last length that fits, and one more, at the 32-bit ceiling (which is the machine's
    // `usize::MAX` on a 32-bit target, and tighter than it on a 64-bit one).
    assert!(store_room(top - cap, cap) && !store_room(top - cap + 1, cap));
    assert!(chains_room(top - 3) && !chains_room(top - 2));
    // And the checks the call-time function makes, by name.
    let fails = |f: &dyn Fn()| {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(f))
            .err()
            .and_then(|p| p.downcast_ref::<String>().cloned())
            .unwrap_or_default()
    };
    assert!(fails(&|| check_room("neg", top - 1999, 0, 0)).contains("classicalStore"));
    assert!(fails(&|| check_room("neg", 0, top - 1999, 0)).contains("sparseStore"));
    assert!(fails(&|| check_room("neg", 0, 0, top - 2)).contains("sparseChainsRoom"));
    check_room("neg", top - cap, top - sparse_cap, top - 3);
    // `usize::MAX` itself, where it is wider than 32 bits.
    assert!(!store_room(usize::MAX - cap + 1, cap));
    assert!(!chains_room(usize::MAX - 1));
}

/// The event bound is one stricter than the invariant's: a state with `events = u32::MAX - 1`
/// imports (`Session::invariant` allows it) and falls outside `classicalEvents`.
#[test]
fn a_session_the_invariant_accepts_can_fall_outside_the_event_ceiling() {
    let (_, bob) = answered_pair();
    let mut bytes = bob.export().to_vec();
    // session: version(1) || len(4) || triple_state; triple_state: version(1) || len(4) ||
    // ratchet_state, so the ratchet state starts at byte 10 and `events` is 176 bytes in.
    let at = 10 + 176;
    assert_eq!(be32(&bytes, at), observe(&bob).events);
    bytes[at..at + 4].copy_from_slice(&(u32::MAX - 1).to_be_bytes());
    let edge = Session::import(&bytes).expect("the invariant allows events = u32::MAX - 1");
    assert!(edge.invariant());
    let observed = observe(&edge);
    assert_eq!(observed.events, u32::MAX - 1);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        check_premises("edge", &observed, None)
    }));
    let message = result
        .err()
        .and_then(|p| p.downcast_ref::<String>().cloned())
        .unwrap_or_default();
    assert!(
        message.contains("classicalEvents"),
        "the premise check let events = u32::MAX - 1 through: {message:?}"
    );
}
