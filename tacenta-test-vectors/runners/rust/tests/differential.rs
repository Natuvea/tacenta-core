//! Differential testing between `tacenta-model` and `tacenta-core`
//! (ADR-0008, practice 9).
//!
//! The committed vectors pin cases someone chose. This runs *generated*
//! operation sequences through both sides and compares them step by step, so
//! that a disagreement nobody thought to write down still shows up. Under
//! ADR-0006 the model is normative, so a disagreement here is a finding: it is
//! reported with the seed, the minimal sequence and the bytes, and is not
//! patched out on either side.
//!
//! ## How it works
//!
//! One generator, blind to both sides. From a seed this file builds a start
//! and a list of operations, encoded as `tacenta-test-vectors/README.md` lays
//! out the `steps` input of `vectors/persistence/ratchet-state.json` and
//! `sparse-ratchet-state.json`. It never asks either side what to generate
//! next and holds no expectation of its own: every comparison below is
//! model against crate.
//!
//! The operations go to `lake exe difftest` (`tacenta-model/Difftest.lean`),
//! which runs them through `Model.Ratchet` or `Model.SparseRatchet` and prints,
//! after the start and after every step, whether the step was taken or refused
//! and the bytes `Model.PersistedState` writes the state as. The same
//! operations are then replayed here on `tacenta-ratchet` and `tacenta-spqr`,
//! and the two transcripts are compared:
//!
//! - **the outcome**, taken or refused, at every step;
//! - **the persisted bytes** after every step, a refused one included -- the
//!   model's operations leave the state alone when they refuse, and the crates
//!   document that a state which returned `Err` is spent and the caller works
//!   on a copy, so this replays on a copy and restores it, as the session layer
//!   does. A skipped key that was not erased, or one erased that should not
//!   have been, is a difference in these bytes;
//! - **the export-and-import check at every step**, rather than at chosen
//!   points: each side reads back the bytes it just wrote, and the two must
//!   agree on whether the reader accepts them and, if it refuses, on which
//!   refusal;
//! - **the refusal kind on an import**, `wrong-version` against
//!   `short-or-malformed` (session-persistence.md, Rejection), on the corrupted
//!   buffers generated after each sequence;
//! - **counter exhaustion**: a step `tacenta-core` refuses as `ChainExhausted`
//!   must be one the model refuses with the counter at its ceiling. The
//!   converse is not asserted and does not hold -- a receive at `nr =
//!   u32::MAX` numbered below it is out of order on both sides, not exhaustion.
//!
//! ## The two composed formats
//!
//! `check_composed` adds the Triple Ratchet and the Braid, whose stored
//! formats the model now states as well.
//!
//! - **The Triple Ratchet** is driven exactly as the two leaves are:
//!   generated operation sequences from fresh starts and from stored bytes
//!   this file assembles at each half's ceiling, with the outcome, the stored
//!   bytes and the export-and-import check compared at every step, and
//!   corrupted imports of the states they reach. A step either half refuses as
//!   `ChainExhausted` must be one the model refuses at a ceiling.
//! - **The Braid** is driven as far as it can be. Its stored states are
//!   assembled here from the layout in `session-persistence.md`, Braid, and
//!   both readers are given each one and four corruptions of it. Its *state
//!   machine* is reached only from `Ct2Sampled`: transition (13) and the
//!   refusal at the reserved epoch read the stored epoch and the message and
//!   nothing else, so they can be run without a KEM value. Every other
//!   transition consumes a key pair or an encapsulation state, whose layout
//!   `session-persistence.md` delegates (ADR-0006, point 5), so neither side
//!   of this harness can build one.
//!
//!   For the same reason, **tags 1 to 4 appear only at a `key_pair` length
//!   both readers refuse.** The page has the reader validate the `header` and
//!   `ek_vector` inside a stored key pair, and finding them needs that layout;
//!   the model states no such rule and so accepts key pairs `tacenta-braid`
//!   refuses. Generating one would be generating a disagreement this harness
//!   is not entitled to report as a finding, so it generates none, and
//!   `ASSURANCE.md` and the conformance manifest record the gap instead.
//!
//! The states are compared by their bytes because neither crate exposes a
//! state's fields or compares two states outside its own tests, the same
//! reason `tests/persistence.rs` gives.
//!
//! ## The ceilings
//!
//! A counter cannot be walked to its ceiling: no run sends 2^32 messages. So
//! the near-ceiling sequences start from stored bytes this file assembles from
//! the layout in `session-persistence.md` -- not from either implementation --
//! and both sides read them. `observed` below asserts that the run actually
//! reached each ceiling, so a generator that stopped reaching them fails here
//! rather than passing on fewer.
//!
//! ## Running it
//!
//! The bounded run is what `cargo test` does: `SEQUENCES` sequences from
//! `SEED`, both printed. A longer run is
//!
//! ```text
//! TACENTA_DIFF_SEQUENCES=2000 cargo test --release --test differential -- --nocapture
//! ```
//!
//! and `TACENTA_DIFF_SEED` picks a different seed. `TACENTA_DIFF_LONG=1` adds
//! the sequences that are too slow for the gate, which the constant below
//! names.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use tacenta_core::ratchet::{self, LabelSet, RatchetDecodeError, RatchetError};
use tacenta_spqr::{Direction, Output, SpqrDecodeError, SpqrError};

/// How many sequences the gate runs, per ratchet. Enough that every start
/// template below is used several times, and short enough that the whole test
/// is a fraction of the Rust suite it runs beside.
const SEQUENCES: usize = 48;

/// The seed the gate runs from. Fixed, so a failure is reproducible from what
/// the test prints; `TACENTA_DIFF_SEED` overrides it.
const SEED: u64 = 0x7ace_07a0_d1ff_0008;

/// The most operations in one sequence.
const STEPS: usize = 20;

/// The largest skip a generated receive asks for and the model may accept.
///
/// The per-chain bound is `MAX_SKIP = 1000` on both sides. Asking for it means
/// deriving a thousand message keys in the model, whose SHA-256 is written in
/// Lean, and then reading a state holding a thousand stored keys back at every
/// later step, which is quadratic in the store. That is minutes rather than
/// seconds, so the gate asks for skips up to this and `TACENTA_DIFF_LONG=1`
/// asks for the bound itself and the step past it. The step *past* the bound
/// is cheap on both sides -- it is refused before anything is derived -- so the
/// gate always includes it.
const GATE_SKIP: u32 = 24;

/// The per-chain skip bound both sides hold (`ratchet.md`, Skipped keys;
/// `sparse-pq-ratchet.md`, Skipped keys).
const MAX_SKIP: u32 = 1000;

/// The fixed fields of each stored format, before the counted entries: the
/// classical ratchet's `FIXED_LEN` and the sparse ratchet's `FIXED_PREFIX`.
/// Used only for the one refusal `session-persistence.md`, Rejection, leaves
/// to the implementation; see `refusals_agree`.
const RATCHET_FIXED_LEN: usize = 185;
const SPARSE_FIXED_PREFIX: usize = 46;

// ---------------------------------------------------------------------------
// The model process
// ---------------------------------------------------------------------------

/// Where `lake exe difftest` put its binary, or the path `TACENTA_DIFFTEST`
/// names.
fn difftest_path() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("TACENTA_DIFFTEST") {
        let p = PathBuf::from(p);
        return p.is_file().then_some(p);
    }
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../tacenta-model/.lake/build/bin/difftest");
    p.is_file().then_some(p)
}

/// Every request answered, in order: the lines of each answer before its `end`.
fn ask_model(exe: &Path, requests: &[String]) -> Vec<Vec<String>> {
    use std::io::Write;

    let mut child = Command::new(exe)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("spawn {}: {e}", exe.display()));
    {
        let stdin = child.stdin.as_mut().expect("the model's stdin");
        for r in requests {
            writeln!(stdin, "{r}").expect("write a request");
        }
    }
    let out = child.wait_with_output().expect("the model's output");
    assert!(
        out.status.success(),
        "the model refused the requests: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    let mut answers = Vec::with_capacity(requests.len());
    let mut current = Vec::new();
    for line in String::from_utf8_lossy(&out.stdout).lines() {
        if line == "end" {
            answers.push(std::mem::take(&mut current));
        } else {
            current.push(line.to_string());
        }
    }
    assert!(
        current.is_empty(),
        "the model's last answer has no end line"
    );
    assert_eq!(
        answers.len(),
        requests.len(),
        "the model answered {} of {} requests",
        answers.len(),
        requests.len()
    );
    answers
}

// ---------------------------------------------------------------------------
// The generator's randomness
// ---------------------------------------------------------------------------

/// SplitMix64, written out so that a seed means the same thing on every
/// machine and in every version of this file. The generator is the only user;
/// nothing it produces is a secret.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A value below `n`, which must not be zero.
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }

    fn byte(&mut self) -> u8 {
        self.next_u64() as u8
    }

    /// A 32-byte value that is a canonical X25519 public key: bit 255 clear,
    /// and below p = 2^255 - 19 because the last byte is below `0x7f`
    /// (message-format.md, Curve public keys). A state holding any other
    /// spelling is refused by both readers, which is checked by the corrupted
    /// imports rather than by every state the operations build.
    fn canonical_key(&mut self) -> [u8; 32] {
        let mut k = [0u8; 32];
        for b in k.iter_mut() {
            *b = self.byte();
        }
        k[31] &= 0x3f;
        k
    }

    fn key(&mut self) -> [u8; 32] {
        let mut k = [0u8; 32];
        for b in k.iter_mut() {
            *b = self.byte();
        }
        k
    }
}

// ---------------------------------------------------------------------------
// The operations, encoded as the vectors encode them
// ---------------------------------------------------------------------------

/// One operation on a classical ratchet state.
#[derive(Clone)]
enum RStep {
    Send,
    Receive {
        dh: [u8; 32],
        pn: u32,
        n: u32,
        dh_recv: [u8; 32],
        dh_send: [u8; 32],
        new_pub: [u8; 32],
    },
}

impl RStep {
    /// `00` a send; `01`, the header's `dh(32) || pn(4) || n(4)`, then
    /// `dh_recv(32) || dh_send(32) || new_pub(32)`.
    fn encode(&self, out: &mut Vec<u8>) {
        match self {
            RStep::Send => out.push(0x00),
            RStep::Receive {
                dh,
                pn,
                n,
                dh_recv,
                dh_send,
                new_pub,
            } => {
                out.push(0x01);
                out.extend_from_slice(dh);
                out.extend_from_slice(&pn.to_be_bytes());
                out.extend_from_slice(&n.to_be_bytes());
                out.extend_from_slice(dh_recv);
                out.extend_from_slice(dh_send);
                out.extend_from_slice(new_pub);
            }
        }
    }
}

/// One operation on a sparse ratchet state.
#[derive(Clone)]
enum SStep {
    Send {
        epoch: u64,
        out: Option<(u64, [u8; 32])>,
    },
    Receive {
        epoch: u64,
        out: Option<(u64, [u8; 32])>,
        n: u64,
    },
}

impl SStep {
    /// `op(1) || epoch(8) || output_present(1) || output_epoch(8) ||
    /// output_key(32)`, and a receive's `n(8)` after it.
    fn encode(&self, buf: &mut Vec<u8>) {
        let (op, epoch, out, n) = match self {
            SStep::Send { epoch, out } => (0x00u8, *epoch, *out, None),
            SStep::Receive { epoch, out, n } => (0x01u8, *epoch, *out, Some(*n)),
        };
        buf.push(op);
        buf.extend_from_slice(&epoch.to_be_bytes());
        match out {
            None => buf.extend_from_slice(&[0u8; 41]),
            Some((e, k)) => {
                buf.push(0x01);
                buf.extend_from_slice(&e.to_be_bytes());
                buf.extend_from_slice(&k);
            }
        }
        if let Some(n) = n {
            buf.extend_from_slice(&n.to_be_bytes());
        }
    }
}

fn encode_ratchet(steps: &[RStep]) -> Vec<u8> {
    let mut out = Vec::new();
    for s in steps {
        s.encode(&mut out);
    }
    out
}

fn encode_sparse(steps: &[SStep]) -> Vec<u8> {
    let mut out = Vec::new();
    for s in steps {
        s.encode(&mut out);
    }
    out
}

// ---------------------------------------------------------------------------
// Starts
// ---------------------------------------------------------------------------

/// Where a sequence begins: the model's and the crate's own initialisation
/// from the same parameters, or stored bytes both sides read.
#[derive(Clone)]
enum Start {
    Fresh(Vec<u8>),
    Stored(Vec<u8>),
}

impl Start {
    fn request(&self, algorithm: &str, steps: &[u8]) -> String {
        let (kind, payload) = match self {
            Start::Fresh(b) => ("fresh", b),
            Start::Stored(b) => ("stored", b),
        };
        format!(
            "run {algorithm} {kind} {} {}",
            hex::encode(payload),
            hex::encode(steps)
        )
    }
}

/// One stored skipped key: its ratchet public key, its message number, the
/// clock reading it was stored at, and the key.
type Skipped = ([u8; 32], u32, u32, [u8; 32]);

/// A classical ratchet state's stored bytes, assembled from the layout in
/// `session-persistence.md`, Ratchet state, rather than by either
/// implementation.
#[allow(clippy::too_many_arguments)]
fn ratchet_state_bytes(
    dhs_pub: &[u8; 32],
    dhr_pub: Option<&[u8; 32]>,
    rk: &[u8; 32],
    cks: Option<&[u8; 32]>,
    ckr: Option<&[u8; 32]>,
    ns: u32,
    nr: u32,
    pn: u32,
    events: u32,
    skipped: &[Skipped],
) -> Vec<u8> {
    fn optional(out: &mut Vec<u8>, k: Option<&[u8; 32]>) {
        match k {
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
    let mut out = vec![0x01];
    out.extend_from_slice(dhs_pub);
    optional(&mut out, dhr_pub);
    out.extend_from_slice(rk);
    optional(&mut out, cks);
    optional(&mut out, ckr);
    out.extend_from_slice(&ns.to_be_bytes());
    out.extend_from_slice(&nr.to_be_bytes());
    out.extend_from_slice(&pn.to_be_bytes());
    out.extend_from_slice(&events.to_be_bytes());
    out.push(0x00); // labels
    out.extend_from_slice(&(skipped.len() as u32).to_be_bytes());
    for (dh, n, stored_at, key) in skipped {
        out.extend_from_slice(dh);
        out.extend_from_slice(&n.to_be_bytes());
        out.extend_from_slice(&stored_at.to_be_bytes());
        out.extend_from_slice(key);
    }
    out
}

/// A sparse ratchet state's stored bytes, one `chains` entry for the current
/// epoch and an empty store (`session-persistence.md`, Sparse ratchet state).
fn sparse_state_bytes(
    rk: &[u8; 32],
    epoch: u64,
    direction: u8,
    send: Option<(&[u8; 32], u64)>,
    receive: Option<(&[u8; 32], u64)>,
    skipped: &[(u64, u64, [u8; 32])],
) -> Vec<u8> {
    fn chain(out: &mut Vec<u8>, c: Option<(&[u8; 32], u64)>) {
        match c {
            None => {
                out.push(0x00);
                out.extend_from_slice(&[0u8; 40]);
            }
            Some((ck, n)) => {
                out.push(0x01);
                out.extend_from_slice(ck);
                out.extend_from_slice(&n.to_be_bytes());
            }
        }
    }
    let mut out = vec![0x01];
    out.extend_from_slice(rk);
    out.extend_from_slice(&epoch.to_be_bytes());
    out.push(direction);
    out.extend_from_slice(&1u32.to_be_bytes()); // one chains entry
    out.extend_from_slice(&epoch.to_be_bytes());
    chain(&mut out, send);
    chain(&mut out, receive);
    out.extend_from_slice(&(skipped.len() as u32).to_be_bytes());
    for (e, n, key) in skipped {
        out.extend_from_slice(&e.to_be_bytes());
        out.extend_from_slice(&n.to_be_bytes());
        out.extend_from_slice(key);
    }
    out
}

// ---------------------------------------------------------------------------
// Reading the model's answer
// ---------------------------------------------------------------------------

enum ModelStart {
    Ok { bytes: Vec<u8>, readback: String },
    Refused(String),
}

enum ModelStep {
    Ok {
        bytes: Vec<u8>,
        readback: String,
    },
    Refused {
        ceiling: bool,
        bytes: Vec<u8>,
        readback: String,
    },
}

fn parse_start(line: &str) -> Result<ModelStart, String> {
    let f: Vec<&str> = line.split(' ').collect();
    match f.as_slice() {
        ["start", "ok", bytes, readback] => Ok(ModelStart::Ok {
            bytes: hex::decode(bytes).map_err(|e| format!("start bytes: {e}"))?,
            readback: (*readback).to_string(),
        }),
        ["start", "refused", kind] => Ok(ModelStart::Refused((*kind).to_string())),
        _ => Err(format!("not a start line: {line}")),
    }
}

fn parse_step(line: &str) -> Result<ModelStep, String> {
    let f: Vec<&str> = line.split(' ').collect();
    match f.as_slice() {
        ["step", _, "ok", bytes, readback] => Ok(ModelStep::Ok {
            bytes: hex::decode(bytes).map_err(|e| format!("step bytes: {e}"))?,
            readback: (*readback).to_string(),
        }),
        ["step", _, "refused", ceiling, bytes, readback] => Ok(ModelStep::Refused {
            ceiling: *ceiling == "ceiling",
            bytes: hex::decode(bytes).map_err(|e| format!("step bytes: {e}"))?,
            readback: (*readback).to_string(),
        }),
        _ => Err(format!("not a step line: {line}")),
    }
}

fn parse_read(line: &str) -> Result<Option<Vec<u8>>, String> {
    let f: Vec<&str> = line.split(' ').collect();
    match f.as_slice() {
        ["read", "ok", bytes] => Ok(Some(
            hex::decode(bytes).map_err(|e| format!("read bytes: {e}"))?,
        )),
        ["read", "refused", _] => Ok(None),
        _ => Err(format!("not a read line: {line}")),
    }
}

fn read_refusal(line: &str) -> Option<String> {
    line.strip_prefix("read refused ").map(str::to_string)
}

// ---------------------------------------------------------------------------
// Refusal kinds
// ---------------------------------------------------------------------------

fn ratchet_kind(e: RatchetDecodeError) -> &'static str {
    match e {
        RatchetDecodeError::UnknownVersion => "wrong-version",
        RatchetDecodeError::TooShort | RatchetDecodeError::Malformed => "short-or-malformed",
    }
}

fn sparse_kind(e: SpqrDecodeError) -> &'static str {
    match e {
        SpqrDecodeError::UnknownVersion => "wrong-version",
        SpqrDecodeError::TooShort | SpqrDecodeError::Malformed => "short-or-malformed",
    }
}

/// Whether two refusals of the same buffer are the same refusal, or the one
/// case `session-persistence.md`, Rejection, leaves to the implementation: a
/// buffer too short for its fixed fields whose version byte is not `0x01` may
/// be refused as either, and `Model.PersistedState` reads the version first
/// while both crates check the length first. `tacenta-test-vectors/README.md`
/// records the same divergence as something no vector pins.
fn refusals_agree(bytes: &[u8], fixed_len: usize, model: &str, rust: &str) -> bool {
    model == rust
        || (bytes.len() < fixed_len
            && bytes.first() != Some(&0x01)
            && model == "wrong-version"
            && rust == "short-or-malformed")
}

// ---------------------------------------------------------------------------
// What the run reached
// ---------------------------------------------------------------------------

/// What the run actually exercised. Asserted at the end, so a generator that
/// stopped reaching the ceilings, the skips or the refusals fails here rather
/// than reporting a green run over fewer cases.
#[derive(Default)]
struct Observed {
    steps: usize,
    accepted: usize,
    refused: usize,
    ratchet_send_ceiling: usize,
    ratchet_receive_ceiling: usize,
    sparse_epoch_ceiling: usize,
    sparse_send_ceiling: usize,
    sparse_receive_ceiling: usize,
    dh_steps: usize,
    keys_stored: usize,
    keys_used: usize,
    store_shrank_beyond_one: usize,
    skip_refused: usize,
    imports: usize,
    imports_accepted: usize,
    imports_wrong_version: usize,
    imports_malformed: usize,
    // The two composed formats.
    triple_steps: usize,
    triple_ceiling: usize,
    triple_reads: usize,
    triple_reads_accepted: usize,
    braid_steps: usize,
    braid_reads: usize,
    braid_reads_accepted: usize,
    braid_ceiling_stepped: usize,
    braid_ceiling_failed: usize,
}

// ---------------------------------------------------------------------------
// The classical ratchet
// ---------------------------------------------------------------------------

/// The readback the model prints, computed on this side: the crate's reader
/// run on the bytes the crate just wrote. `same` compares bytes rather than
/// states because the crate exposes no state comparison; by
/// `RatchetState.ofBytes_ok` an accepted buffer and the state it holds
/// determine each other, so the two readings agree.
fn ratchet_readback(bytes: &[u8]) -> String {
    match ratchet::State::from_bytes(bytes) {
        Ok(s) => {
            if s.to_bytes().as_slice() == bytes {
                "same".to_string()
            } else {
                "differs".to_string()
            }
        }
        Err(e) => format!("refused:{}", ratchet_kind(e)),
    }
}

fn sparse_readback(bytes: &[u8]) -> String {
    match tacenta_spqr::State::from_bytes(bytes) {
        Ok(s) => {
            if s.to_bytes().as_slice() == bytes {
                "same".to_string()
            } else {
                "differs".to_string()
            }
        }
        Err(e) => format!("refused:{}", sparse_kind(e)),
    }
}

/// Replay one classical sequence on `tacenta-ratchet` against the model's
/// answer. `Err` is a disagreement, described for the report.
fn check_ratchet(
    start: &Start,
    steps: &[RStep],
    answer: &[String],
    seen: &mut Observed,
) -> Result<(), String> {
    let mut lines = answer.iter();
    let first = lines.next().ok_or("the model answered nothing")?;
    let want = parse_start(first)?;

    let mut state = match start {
        Start::Fresh(p) => {
            let sk: [u8; 32] = p[1..33].try_into().map_err(|_| "a short fresh start")?;
            let our: [u8; 32] = p[33..65].try_into().map_err(|_| "a short fresh start")?;
            let st = match p[0] {
                0x00 => ratchet::init_sender(
                    &sk,
                    our,
                    p[65..97].try_into().map_err(|_| "a short fresh start")?,
                    &p[97..129].try_into().map_err(|_| "a short fresh start")?,
                    LabelSet::Tacenta,
                ),
                _ => ratchet::init_receiver(&sk, our, LabelSet::Tacenta),
            };
            match want {
                ModelStart::Ok { bytes, readback } => {
                    let got = st.to_bytes();
                    if got.as_slice() != bytes {
                        return Err(format!(
                            "initialisation: the crate writes {}, the model {}",
                            hex::encode(got.as_slice()),
                            hex::encode(&bytes)
                        ));
                    }
                    let mine = ratchet_readback(got.as_slice());
                    if mine != readback {
                        return Err(format!(
                            "initialisation read back: the crate says {mine}, the model {readback}"
                        ));
                    }
                }
                ModelStart::Refused(kind) => {
                    return Err(format!(
                        "initialisation: the model refuses it as {kind}, the crate takes it"
                    ));
                }
            }
            st
        }
        Start::Stored(bytes) => match (ratchet::State::from_bytes(bytes), want) {
            (Ok(st), ModelStart::Ok { bytes: want, .. }) => {
                let got = st.to_bytes();
                if got.as_slice() != want {
                    return Err(format!(
                        "the stored start: the crate reads it back as {}, the model as {}",
                        hex::encode(got.as_slice()),
                        hex::encode(&want)
                    ));
                }
                st
            }
            (Err(e), ModelStart::Refused(kind)) => {
                let mine = ratchet_kind(e);
                if !refusals_agree(bytes, RATCHET_FIXED_LEN, &kind, mine) {
                    return Err(format!(
                        "the stored start: the crate refuses it as {mine}, the model as {kind}"
                    ));
                }
                return Ok(());
            }
            (Ok(_), ModelStart::Refused(kind)) => {
                return Err(format!(
                    "the stored start: the model refuses it as {kind}, the crate accepts it"
                ));
            }
            (Err(e), ModelStart::Ok { .. }) => {
                return Err(format!(
                    "the stored start: the crate refuses it ({e:?}), the model accepts it"
                ));
            }
        },
    };

    for (i, step) in steps.iter().enumerate() {
        let line = lines
            .next()
            .ok_or_else(|| format!("step {}: the model answered nothing", i + 1))?;
        let want = parse_step(line)?;
        // The crate documents that a state which returned `Err` is spent and
        // that a caller works on a copy, as the session layer does. The copy
        // is what lets a sequence carry on past a refusal and still compare
        // the bytes the refusal left.
        let before = state.clone();
        let public_before = state.sending_public();
        let stored_before = state.skipped_len();
        let outcome = match step {
            RStep::Send => ratchet::send(&mut state).map(|_| ()),
            RStep::Receive {
                dh,
                pn,
                n,
                dh_recv,
                dh_send,
                new_pub,
            } => ratchet::receive(
                &mut state,
                &ratchet::Header {
                    dh: *dh,
                    pn: *pn,
                    n: *n,
                },
                dh_recv,
                dh_send,
                *new_pub,
            )
            .map(|_| ()),
        };
        seen.steps += 1;
        match (outcome, want) {
            (Ok(()), ModelStep::Ok { bytes, readback }) => {
                seen.accepted += 1;
                if state.sending_public() != public_before {
                    seen.dh_steps += 1;
                }
                let after = state.skipped_len();
                if after > stored_before {
                    seen.keys_stored += 1;
                } else if after + 1 == stored_before {
                    seen.keys_used += 1;
                } else if after < stored_before {
                    // More than one key left the store at once, which no
                    // single message takes: the classical store ageing keys
                    // out, or a sparse epoch retiring with its keys.
                    seen.store_shrank_beyond_one += 1;
                }
                compare_state(i + 1, state.to_bytes().as_slice(), &bytes, &readback, &{
                    ratchet_readback(state.to_bytes().as_slice())
                })?;
            }
            (
                Err(e),
                ModelStep::Refused {
                    ceiling,
                    bytes,
                    readback,
                },
            ) => {
                seen.refused += 1;
                if e == RatchetError::TooManySkipped || e == RatchetError::SkippedStoreFull {
                    seen.skip_refused += 1;
                }
                if e == RatchetError::ChainExhausted {
                    if !ceiling {
                        return Err(format!(
                            "step {}: the crate refuses it as ChainExhausted, \
                             and the model's counter is not at its ceiling",
                            i + 1
                        ));
                    }
                    match step {
                        RStep::Send => seen.ratchet_send_ceiling += 1,
                        RStep::Receive { .. } => seen.ratchet_receive_ceiling += 1,
                    }
                }
                state = before;
                compare_state(i + 1, state.to_bytes().as_slice(), &bytes, &readback, &{
                    ratchet_readback(state.to_bytes().as_slice())
                })?;
            }
            (Ok(()), ModelStep::Refused { .. }) => {
                return Err(format!(
                    "step {}: the crate takes it, the model refuses it",
                    i + 1
                ));
            }
            (Err(e), ModelStep::Ok { .. }) => {
                return Err(format!(
                    "step {}: the crate refuses it ({e:?}), the model takes it",
                    i + 1
                ));
            }
        }
    }
    Ok(())
}

/// The bytes and the readback of one step, on both sides.
fn compare_state(
    step: usize,
    got: &[u8],
    want: &[u8],
    want_readback: &str,
    got_readback: &str,
) -> Result<(), String> {
    if got != want {
        return Err(format!(
            "step {step}: the crate writes {}, the model {}",
            hex::encode(got),
            hex::encode(want)
        ));
    }
    if got_readback != want_readback {
        return Err(format!(
            "step {step}: read back, the crate says {got_readback}, the model {want_readback}"
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The sparse ratchet
// ---------------------------------------------------------------------------

fn check_sparse(
    start: &Start,
    steps: &[SStep],
    answer: &[String],
    seen: &mut Observed,
) -> Result<(), String> {
    use tacenta_spqr::State;

    let mut lines = answer.iter();
    let first = lines.next().ok_or("the model answered nothing")?;
    let want = parse_start(first)?;

    let mut state = match start {
        Start::Fresh(p) => {
            let st = match p[0] {
                0x00 => State::init(&p[1..33], Direction::A2b),
                _ => State::init(&p[1..33], Direction::B2a),
            };
            match want {
                ModelStart::Ok { bytes, readback } => {
                    let got = st.to_bytes();
                    if got.as_slice() != bytes {
                        return Err(format!(
                            "initialisation: the crate writes {}, the model {}",
                            hex::encode(got.as_slice()),
                            hex::encode(&bytes)
                        ));
                    }
                    let mine = sparse_readback(got.as_slice());
                    if mine != readback {
                        return Err(format!(
                            "initialisation read back: the crate says {mine}, the model {readback}"
                        ));
                    }
                }
                ModelStart::Refused(kind) => {
                    return Err(format!(
                        "initialisation: the model refuses it as {kind}, the crate takes it"
                    ));
                }
            }
            st
        }
        Start::Stored(bytes) => match (State::from_bytes(bytes), want) {
            (Ok(st), ModelStart::Ok { bytes: want, .. }) => {
                let got = st.to_bytes();
                if got.as_slice() != want {
                    return Err(format!(
                        "the stored start: the crate reads it back as {}, the model as {}",
                        hex::encode(got.as_slice()),
                        hex::encode(&want)
                    ));
                }
                st
            }
            (Err(e), ModelStart::Refused(kind)) => {
                let mine = sparse_kind(e);
                if !refusals_agree(bytes, SPARSE_FIXED_PREFIX, &kind, mine) {
                    return Err(format!(
                        "the stored start: the crate refuses it as {mine}, the model as {kind}"
                    ));
                }
                return Ok(());
            }
            (Ok(_), ModelStart::Refused(kind)) => {
                return Err(format!(
                    "the stored start: the model refuses it as {kind}, the crate accepts it"
                ));
            }
            (Err(e), ModelStart::Ok { .. }) => {
                return Err(format!(
                    "the stored start: the crate refuses it ({e:?}), the model accepts it"
                ));
            }
        },
    };

    for (i, step) in steps.iter().enumerate() {
        let line = lines
            .next()
            .ok_or_else(|| format!("step {}: the model answered nothing", i + 1))?;
        let want = parse_step(line)?;
        let before = state.clone();
        let epoch_before = state.epoch();
        let stored_before = state.skipped_len();
        let outcome = match step {
            SStep::Send { epoch, out } => {
                let o = out.map(|(e, k)| Output::new(e, k));
                state.send(*epoch, o.as_ref()).map(|_| ())
            }
            SStep::Receive { epoch, out, n } => {
                let o = out.map(|(e, k)| Output::new(e, k));
                state.receive(*epoch, o.as_ref(), *n).map(|_| ())
            }
        };
        seen.steps += 1;
        match (outcome, want) {
            (Ok(()), ModelStep::Ok { bytes, readback }) => {
                seen.accepted += 1;
                if state.epoch() != epoch_before {
                    seen.dh_steps += 1;
                }
                let after = state.skipped_len();
                if after > stored_before {
                    seen.keys_stored += 1;
                } else if after + 1 == stored_before {
                    seen.keys_used += 1;
                } else if after < stored_before {
                    // More than one key left the store at once, which no
                    // single message takes: the classical store ageing keys
                    // out, or a sparse epoch retiring with its keys.
                    seen.store_shrank_beyond_one += 1;
                }
                compare_state(i + 1, state.to_bytes().as_slice(), &bytes, &readback, &{
                    sparse_readback(state.to_bytes().as_slice())
                })?;
            }
            (
                Err(e),
                ModelStep::Refused {
                    ceiling,
                    bytes,
                    readback,
                },
            ) => {
                seen.refused += 1;
                if e == SpqrError::TooManySkipped || e == SpqrError::SkippedStoreFull {
                    seen.skip_refused += 1;
                }
                if e == SpqrError::ChainExhausted {
                    if !ceiling {
                        return Err(format!(
                            "step {}: the crate refuses it as ChainExhausted, \
                             and the model's counter is not at its ceiling",
                            i + 1
                        ));
                    }
                    // Which ceiling: the reserved epoch is reached inside the
                    // advance, before the chain is looked up.
                    let advancing = match step {
                        SStep::Send { out, .. } | SStep::Receive { out, .. } => out.is_some(),
                    };
                    if advancing && epoch_before.saturating_add(1) == u64::MAX {
                        seen.sparse_epoch_ceiling += 1;
                    } else {
                        match step {
                            SStep::Send { .. } => seen.sparse_send_ceiling += 1,
                            SStep::Receive { .. } => seen.sparse_receive_ceiling += 1,
                        }
                    }
                }
                state = before;
                compare_state(i + 1, state.to_bytes().as_slice(), &bytes, &readback, &{
                    sparse_readback(state.to_bytes().as_slice())
                })?;
            }
            (Ok(()), ModelStep::Refused { .. }) => {
                return Err(format!(
                    "step {}: the crate takes it, the model refuses it",
                    i + 1
                ));
            }
            (Err(e), ModelStep::Ok { .. }) => {
                return Err(format!(
                    "step {}: the crate refuses it ({e:?}), the model takes it",
                    i + 1
                ));
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Generating a sequence
// ---------------------------------------------------------------------------

/// A generated classical sequence: where it starts, what it does, and what the
/// generator believes the peer's ratchet key and the chain's position are. The
/// belief is used only to *choose* plausible operations; nothing checks
/// against it, and a wrong guess is a refused step the two sides still have to
/// agree about.
struct RatchetSequence {
    start: Start,
    steps: Vec<RStep>,
}

fn generate_ratchet(rng: &mut Rng, template: usize, long: bool) -> RatchetSequence {
    let dhs = rng.canonical_key();
    let dhr = rng.canonical_key();
    let rk = rng.key();
    let cks = rng.key();
    let ckr = rng.key();
    let ceiling = u32::MAX;

    // Every template in turn, so the ceilings are reached by construction and
    // not by chance. A near-ceiling start is followed by the operation that
    // meets the ceiling; everything after it is generated.
    let (start, mut steps, mut shadow_dhr, mut shadow_nr) = match template % 10 {
        0 | 1 => {
            let role = (template % 10) as u8;
            let mut p = vec![role];
            p.extend_from_slice(&rng.key()); // sk
            p.extend_from_slice(&dhs); // our_pub
            p.extend_from_slice(&dhr); // peer_pub
            p.extend_from_slice(&rng.key()); // dh_out
            (Start::Fresh(p), Vec::new(), None, 0u32)
        }
        2 | 3 => {
            // `ns` at the ceiling and one below it: a send is refused at the
            // first and takes the counter to the ceiling at the second.
            let ns = if template % 10 == 2 {
                ceiling
            } else {
                ceiling - 1
            };
            let b = ratchet_state_bytes(
                &dhs,
                Some(&dhr),
                &rk,
                Some(&cks),
                Some(&ckr),
                ns,
                0,
                0,
                0,
                &[],
            );
            (Start::Stored(b), vec![RStep::Send], Some(dhr), 0)
        }
        4 | 5 => {
            // `nr` at the ceiling and one below it.
            let nr = if template % 10 == 4 {
                ceiling
            } else {
                ceiling - 1
            };
            let b = ratchet_state_bytes(
                &dhs,
                Some(&dhr),
                &rk,
                Some(&cks),
                Some(&ckr),
                0,
                nr,
                0,
                0,
                &[],
            );
            let step = RStep::Receive {
                dh: dhr,
                pn: 0,
                n: nr,
                dh_recv: rng.key(),
                dh_send: rng.key(),
                new_pub: rng.canonical_key(),
            };
            (Start::Stored(b), vec![step], Some(dhr), nr)
        }
        6 | 7 => {
            // The received-message clock at its stop and one below it.
            let events = if template % 10 == 6 {
                ceiling - 1
            } else {
                ceiling - 2
            };
            let b = ratchet_state_bytes(
                &dhs,
                Some(&dhr),
                &rk,
                Some(&cks),
                Some(&ckr),
                0,
                0,
                0,
                events,
                &[],
            );
            (Start::Stored(b), Vec::new(), Some(dhr), 0)
        }
        8 => {
            // A store whose keys are ageing out. `MAX_SKIPPED_AGE` is 1000 on
            // both sides, and an accepted receive counts one message before
            // the store is aged, so from `events = 2000` the keys stored at 0
            // and at 1001 are exactly at or past the age and go, while the one
            // at 1002 is one message short and stays. A key left behind, a key
            // taken early, or an off-by-one in the age is a difference in the
            // bytes the two sides write here.
            let events = 2000u32;
            let store = [
                (dhr, 5u32, 0u32, rng.key()),
                (dhr, 6, events - 999, rng.key()),
                (dhr, 7, events - 998, rng.key()),
            ];
            let b = ratchet_state_bytes(
                &dhs,
                Some(&dhr),
                &rk,
                Some(&cks),
                Some(&ckr),
                0,
                0,
                0,
                events,
                &store,
            );
            let step = RStep::Receive {
                dh: dhr,
                pn: 0,
                n: 0,
                dh_recv: rng.key(),
                dh_send: rng.key(),
                new_pub: rng.canonical_key(),
            };
            (Start::Stored(b), vec![step], Some(dhr), 0)
        }
        _ => {
            // A stored key an imported state can still answer with: the
            // message it belongs to arrives, and the key is taken and removed.
            let store = [(dhr, 9u32, 0u32, rng.key())];
            let b = ratchet_state_bytes(
                &dhs,
                Some(&dhr),
                &rk,
                Some(&cks),
                Some(&ckr),
                0,
                0,
                0,
                0,
                &store,
            );
            let step = RStep::Receive {
                dh: dhr,
                pn: 0,
                n: 9,
                dh_recv: rng.key(),
                dh_send: rng.key(),
                new_pub: rng.canonical_key(),
            };
            (Start::Stored(b), vec![step], Some(dhr), 0)
        }
    };

    // A small pool of ratchet keys, so a peer can leave a key and come back to
    // it, which is what makes the store a map rather than a list.
    let pool: Vec<[u8; 32]> = (0..3).map(|_| rng.canonical_key()).collect();
    let mut used: Vec<([u8; 32], u32, u32)> = Vec::new();

    while steps.len() < STEPS {
        if rng.below(10) < 3 {
            steps.push(RStep::Send);
            continue;
        }
        let dh = match shadow_dhr {
            Some(k) if rng.below(10) < 8 => k,
            _ => {
                let k = pool[rng.below(pool.len() as u64) as usize];
                shadow_dhr = Some(k);
                shadow_nr = 0;
                k
            }
        };
        let n = match rng.below(10) {
            // In order.
            0..=4 => shadow_nr,
            // A small skip, which stores the keys it passes.
            5..=6 => shadow_nr.saturating_add(1 + rng.below(u64::from(GATE_SKIP)) as u32),
            // A duplicate of a message already delivered.
            7 if !used.is_empty() => {
                let (d, _, n) = used[rng.below(used.len() as u64) as usize];
                if d == dh { n } else { shadow_nr }
            }
            // The per-chain bound, and the step past it. Past it is refused
            // before anything is derived, so it is cheap on both sides; the
            // bound itself derives a thousand keys in the model and is left to
            // the long run.
            8 => shadow_nr.saturating_add(MAX_SKIP + 1),
            9 if long => shadow_nr.saturating_add(MAX_SKIP),
            _ => shadow_nr,
        };
        let pn = if rng.below(10) < 8 {
            0
        } else {
            rng.below(4) as u32
        };
        steps.push(RStep::Receive {
            dh,
            pn,
            n,
            dh_recv: rng.key(),
            dh_send: rng.key(),
            new_pub: rng.canonical_key(),
        });
        used.push((dh, pn, n));
        if n >= shadow_nr {
            shadow_nr = n.saturating_add(1);
        }
    }

    RatchetSequence { start, steps }
}

struct SparseSequence {
    start: Start,
    steps: Vec<SStep>,
}

fn generate_sparse(rng: &mut Rng, template: usize, long: bool) -> SparseSequence {
    let rk = rng.key();
    let cks = rng.key();
    let ckr = rng.key();
    let ceiling = u64::MAX;

    let (start, mut steps, mut epoch, mut send_n, mut recv_n) = match template % 10 {
        0 | 1 => {
            let direction = (template % 10) as u8;
            let mut p = vec![direction];
            p.extend_from_slice(&rng.key());
            (Start::Fresh(p), Vec::new(), 0u64, 0u64, 0u64)
        }
        2 | 3 => {
            // A sending chain at the ceiling and one below it.
            let n = if template % 10 == 2 {
                ceiling
            } else {
                ceiling - 1
            };
            let b = sparse_state_bytes(&rk, 0, 0x00, Some((&cks, n)), Some((&ckr, 0)), &[]);
            (
                Start::Stored(b),
                vec![SStep::Send {
                    epoch: 0,
                    out: None,
                }],
                0,
                n,
                0,
            )
        }
        4 | 5 => {
            // A receiving chain at the ceiling and one below it.
            let n = if template % 10 == 4 {
                ceiling
            } else {
                ceiling - 1
            };
            let b = sparse_state_bytes(&rk, 0, 0x01, Some((&cks, 0)), Some((&ckr, n)), &[]);
            (
                Start::Stored(b),
                vec![SStep::Receive {
                    epoch: 0,
                    out: None,
                    n: ceiling,
                }],
                0,
                0,
                n,
            )
        }
        6 | 7 => {
            // The epoch one and two below its reserved value: the advance onto
            // `u64::MAX` is refused, the one onto `u64::MAX - 1` is taken.
            let e = if template % 10 == 6 {
                ceiling - 1
            } else {
                ceiling - 2
            };
            let b = sparse_state_bytes(&rk, e, 0x01, Some((&cks, 0)), Some((&ckr, 0)), &[]);
            (
                Start::Stored(b),
                vec![SStep::Receive {
                    epoch: e,
                    out: Some((e + 1, rng.key())),
                    n: 1,
                }],
                e,
                0,
                0,
            )
        }
        8 => {
            // A stored key an imported state can still answer with.
            let store = [(0u64, 4u64, rng.key())];
            let b = sparse_state_bytes(&rk, 0, 0x01, Some((&cks, 0)), Some((&ckr, 0)), &store);
            (
                Start::Stored(b),
                vec![SStep::Receive {
                    epoch: 0,
                    out: None,
                    n: 4,
                }],
                0,
                0,
                0,
            )
        }
        _ => {
            // Retirement takes an epoch's stored keys with it: `EPOCHS_KEPT`
            // is 2 on both sides, so the second advance puts epoch 0 outside
            // the window and its two stored keys must go with its chains.
            let store = [(0u64, 1u64, rng.key()), (0u64, 2u64, rng.key())];
            let b = sparse_state_bytes(&rk, 0, 0x01, Some((&cks, 0)), Some((&ckr, 0)), &store);
            let opening = vec![
                SStep::Receive {
                    epoch: 1,
                    out: Some((1, rng.key())),
                    n: 1,
                },
                SStep::Receive {
                    epoch: 2,
                    out: Some((2, rng.key())),
                    n: 1,
                },
            ];
            (Start::Stored(b), opening, 2, 0, 1)
        }
    };

    while steps.len() < STEPS {
        // An agreement secret, which opens the next epoch; sometimes one for
        // an epoch that does not follow, which both sides must refuse.
        let out = match rng.below(10) {
            0..=1 => Some((epoch.saturating_add(1), rng.key())),
            2 => Some((epoch.saturating_add(2), rng.key())),
            _ => None,
        };
        // The epoch a message names: the current one, the one the secret
        // opens, or one that has been retired.
        let named = match rng.below(10) {
            0..=6 => match out {
                Some((e, _)) => e,
                None => epoch,
            },
            7..=8 => epoch,
            _ => epoch.saturating_sub(1),
        };
        if rng.below(10) < 4 {
            steps.push(SStep::Send { epoch: named, out });
            if out.map(|(e, _)| e) == Some(epoch.saturating_add(1)) {
                epoch = epoch.saturating_add(1);
                send_n = 0;
                recv_n = 0;
            }
            if named == epoch {
                send_n = send_n.saturating_add(1);
            }
            continue;
        }
        let n = match rng.below(10) {
            0..=4 => recv_n.saturating_add(1),
            5..=6 => recv_n.saturating_add(1 + rng.below(u64::from(GATE_SKIP))),
            7 => recv_n,
            8 => recv_n.saturating_add(u64::from(MAX_SKIP) + 2),
            9 if long => recv_n.saturating_add(u64::from(MAX_SKIP) + 1),
            _ => recv_n.saturating_add(1),
        };
        steps.push(SStep::Receive {
            epoch: named,
            out,
            n,
        });
        if out.map(|(e, _)| e) == Some(epoch.saturating_add(1)) {
            epoch = epoch.saturating_add(1);
            send_n = 0;
            recv_n = 0;
        }
        if named == epoch && n > recv_n {
            recv_n = n;
        }
    }

    SparseSequence { start, steps }
}

// ---------------------------------------------------------------------------
// Corrupted imports
// ---------------------------------------------------------------------------

/// Buffers made from a state's stored bytes by changing one thing: a byte, the
/// version, the length. Both readers must agree on whether each is accepted,
/// on the bytes an accepted one holds, and on which refusal a refused one gets.
fn corrupt(rng: &mut Rng, bytes: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    if bytes.is_empty() {
        return out;
    }
    // One byte changed, anywhere.
    let mut a = bytes.to_vec();
    let at = rng.below(a.len() as u64) as usize;
    a[at] ^= 1 << (rng.below(8) as u32);
    out.push(a);
    // The version byte, which is the one refusal the readers distinguish.
    let mut b = bytes.to_vec();
    b[0] = b[0].wrapping_add(1 + rng.byte() % 8);
    out.push(b);
    // Cut short, and lengthened past the last entry.
    out.push(bytes[..rng.below(bytes.len() as u64) as usize].to_vec());
    let mut d = bytes.to_vec();
    d.push(rng.byte());
    out.push(d);
    out
}

// ---------------------------------------------------------------------------
// The Triple Ratchet and the Braid
// ---------------------------------------------------------------------------

/// The fixed fields of the two composed formats, before anything counted: the
/// triple ratchet state's version byte, and the Braid's version byte and tag.
/// Used only for the one refusal `session-persistence.md`, Rejection, leaves
/// to the implementation; see `refusals_agree`.
const TRIPLE_FIXED_LEN: usize = 1;
const BRAID_FIXED_LEN: usize = 2;

/// The KEM and MAC lengths the Braid's fields have (CONSTANTS.md, Braid KEM
/// field lengths; KEM key pair and encapsulation state lengths). The last two
/// are the values whose layout `session-persistence.md` delegates: this file
/// writes them at the right length and never pretends to their contents.
const HEADER_LEN: usize = 64;
const EK_VECTOR_LEN: usize = 1536;
const CT1_LEN: usize = 1408;
const CT2_LEN: usize = 160;
const MAC_LEN: usize = 32;
const KEY_PAIR_LEN: usize = 11_872;
const ENCAPS_LEN: usize = 2_592;

/// One operation on a Triple Ratchet state, encoded as
/// `vectors/persistence/triple-ratchet-state.json`'s `steps` encodes them.
#[derive(Clone)]
enum TStep {
    Send {
        epoch: u64,
        out: Option<(u64, [u8; 32])>,
    },
    Receive {
        dh: [u8; 32],
        pn: u32,
        n: u32,
        dh_recv: [u8; 32],
        dh_send: [u8; 32],
        new_pub: [u8; 32],
        epoch: u64,
        pq_n: u64,
        out: Option<(u64, [u8; 32])>,
    },
}

/// `output_present(1) || output_epoch(8) || output_key(32)`, zeroed when
/// absent, as both ratchet-state files write one.
fn encode_output(buf: &mut Vec<u8>, out: Option<(u64, [u8; 32])>) {
    match out {
        None => buf.extend_from_slice(&[0u8; 41]),
        Some((e, k)) => {
            buf.push(0x01);
            buf.extend_from_slice(&e.to_be_bytes());
            buf.extend_from_slice(&k);
        }
    }
}

impl TStep {
    fn encode(&self, buf: &mut Vec<u8>) {
        match self {
            TStep::Send { epoch, out } => {
                buf.push(0x00);
                buf.extend_from_slice(&epoch.to_be_bytes());
                encode_output(buf, *out);
            }
            TStep::Receive {
                dh,
                pn,
                n,
                dh_recv,
                dh_send,
                new_pub,
                epoch,
                pq_n,
                out,
            } => {
                buf.push(0x01);
                buf.extend_from_slice(dh);
                buf.extend_from_slice(&pn.to_be_bytes());
                buf.extend_from_slice(&n.to_be_bytes());
                buf.extend_from_slice(dh_recv);
                buf.extend_from_slice(dh_send);
                buf.extend_from_slice(new_pub);
                buf.extend_from_slice(&epoch.to_be_bytes());
                buf.extend_from_slice(&pq_n.to_be_bytes());
                encode_output(buf, *out);
            }
        }
    }
}

fn encode_triple(steps: &[TStep]) -> Vec<u8> {
    let mut out = Vec::new();
    for s in steps {
        s.encode(&mut out);
    }
    out
}

/// A Triple Ratchet state's stored bytes, assembled from the layout in
/// `session-persistence.md`, Triple ratchet state, over the two halves the
/// assemblers above build.
fn triple_state_bytes(classical: &[u8], post_quantum: &[u8]) -> Vec<u8> {
    let mut out = vec![0x01];
    out.extend_from_slice(&(classical.len() as u32).to_be_bytes());
    out.extend_from_slice(classical);
    out.extend_from_slice(&(post_quantum.len() as u32).to_be_bytes());
    out.extend_from_slice(post_quantum);
    out
}

fn triple_kind(e: tacenta_triple::TripleDecodeError) -> &'static str {
    use tacenta_triple::TripleDecodeError as E;
    match e {
        E::UnknownVersion => "wrong-version",
        E::TooShort | E::Malformed => "short-or-malformed",
    }
}

fn triple_readback(bytes: &[u8]) -> String {
    match tacenta_triple::State::from_bytes(bytes) {
        Ok(s) => {
            if s.to_bytes().as_slice() == bytes {
                "same".to_string()
            } else {
                "differs".to_string()
            }
        }
        Err(e) => format!("refused:{}", triple_kind(e)),
    }
}

/// Replay one Triple Ratchet sequence against the model's answer.
fn check_triple(
    start: &Start,
    steps: &[TStep],
    answer: &[String],
    seen: &mut Observed,
) -> Result<(), String> {
    use tacenta_triple::{DrHeader, Header, LabelSet, Output, State};

    let mut lines = answer.iter();
    let first = lines.next().ok_or("the model answered nothing")?;
    let want = parse_start(first)?;

    let mut state = match start {
        Start::Fresh(p) => {
            let sk: [u8; 32] = p[1..33].try_into().map_err(|_| "a short fresh start")?;
            let our: [u8; 32] = p[33..65].try_into().map_err(|_| "a short fresh start")?;
            let st = match p[0] {
                0x00 => State::init_sender(
                    &sk,
                    our,
                    p[65..97].try_into().map_err(|_| "a short fresh start")?,
                    &p[97..129].try_into().map_err(|_| "a short fresh start")?,
                    LabelSet::Tacenta,
                ),
                _ => State::init_receiver(&sk, our, LabelSet::Tacenta),
            };
            match want {
                ModelStart::Ok { bytes, readback } => {
                    let got = st.to_bytes();
                    if got.as_slice() != bytes {
                        return Err(format!(
                            "initialisation: the crate writes {}, the model {}",
                            hex::encode(got.as_slice()),
                            hex::encode(&bytes)
                        ));
                    }
                    let mine = triple_readback(got.as_slice());
                    if mine != readback {
                        return Err(format!(
                            "initialisation read back: the crate says {mine}, the model {readback}"
                        ));
                    }
                }
                ModelStart::Refused(kind) => {
                    return Err(format!(
                        "initialisation: the model refuses it as {kind}, the crate takes it"
                    ));
                }
            }
            st
        }
        Start::Stored(bytes) => match (State::from_bytes(bytes), want) {
            (Ok(st), ModelStart::Ok { bytes: want, .. }) => {
                let got = st.to_bytes();
                if got.as_slice() != want {
                    return Err(format!(
                        "the stored start: the crate reads it back as {}, the model as {}",
                        hex::encode(got.as_slice()),
                        hex::encode(&want)
                    ));
                }
                st
            }
            (Err(e), ModelStart::Refused(kind)) => {
                let mine = triple_kind(e);
                if !refusals_agree(bytes, TRIPLE_FIXED_LEN, &kind, mine) {
                    return Err(format!(
                        "the stored start: the crate refuses it as {mine}, the model as {kind}"
                    ));
                }
                return Ok(());
            }
            (Ok(_), ModelStart::Refused(kind)) => {
                return Err(format!(
                    "the stored start: the model refuses it as {kind}, the crate accepts it"
                ));
            }
            (Err(e), ModelStart::Ok { .. }) => {
                return Err(format!(
                    "the stored start: the crate refuses it ({e:?}), the model accepts it"
                ));
            }
        },
    };

    for (i, step) in steps.iter().enumerate() {
        let line = lines
            .next()
            .ok_or_else(|| format!("step {}: the model answered nothing", i + 1))?;
        let want = parse_step(line)?;
        let before = state.clone();
        let outcome = match step {
            TStep::Send { epoch, out } => {
                let o = out.map(|(e, k)| Output::new(e, k));
                state.send(*epoch, o.as_ref()).map(|_| ())
            }
            TStep::Receive {
                dh,
                pn,
                n,
                dh_recv,
                dh_send,
                new_pub,
                epoch,
                pq_n,
                out,
            } => {
                let o = out.map(|(e, k)| Output::new(e, k));
                let header = Header {
                    dr: DrHeader {
                        dh: *dh,
                        pn: *pn,
                        n: *n,
                    },
                    epoch: *epoch,
                    pq_n: *pq_n,
                };
                // A receive returns a candidate the caller commits once the
                // message has authenticated, which is what the session does.
                match state.receive(&header, dh_recv, dh_send, *new_pub, o.as_ref()) {
                    Ok((next, _key)) => {
                        state.commit(next);
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            }
        };
        seen.steps += 1;
        seen.triple_steps += 1;
        match (outcome, want) {
            (Ok(()), ModelStep::Ok { bytes, readback }) => {
                seen.accepted += 1;
                compare_state(i + 1, state.to_bytes().as_slice(), &bytes, &readback, &{
                    triple_readback(state.to_bytes().as_slice())
                })?;
            }
            (
                Err(e),
                ModelStep::Refused {
                    ceiling,
                    bytes,
                    readback,
                },
            ) => {
                seen.refused += 1;
                let exhausted = matches!(
                    e,
                    tacenta_triple::TripleError::Classical(RatchetError::ChainExhausted)
                        | tacenta_triple::TripleError::PostQuantum(SpqrError::ChainExhausted)
                );
                if exhausted {
                    if !ceiling {
                        return Err(format!(
                            "step {}: the crate refuses it as ChainExhausted, \
                             and neither of the model's halves is at a ceiling",
                            i + 1
                        ));
                    }
                    seen.triple_ceiling += 1;
                }
                state = before;
                compare_state(i + 1, state.to_bytes().as_slice(), &bytes, &readback, &{
                    triple_readback(state.to_bytes().as_slice())
                })?;
            }
            (Ok(()), ModelStep::Refused { .. }) => {
                return Err(format!(
                    "step {}: the crate takes it, the model refuses it",
                    i + 1
                ));
            }
            (Err(e), ModelStep::Ok { .. }) => {
                return Err(format!(
                    "step {}: the crate refuses it ({e:?}), the model takes it",
                    i + 1
                ));
            }
        }
    }
    Ok(())
}

struct TripleSequence {
    start: Start,
    steps: Vec<TStep>,
}

/// A generated Triple Ratchet sequence. The near-ceiling starts are assembled
/// from the two halves' layouts, as the leaves' are, because neither counter
/// can be walked to. Every stored start here gives the classical half both
/// chains, so it shows no role and the composition's rule holds vacuously;
/// the role rule itself is pinned by the vectors, which can build a state
/// that breaks it.
fn generate_triple(rng: &mut Rng, template: usize, _long: bool) -> TripleSequence {
    let dhs = rng.canonical_key();
    let dhr = rng.canonical_key();
    let rk = rng.key();
    let cks = rng.key();
    let ckr = rng.key();

    let both_chains = |ns: u32, nr: u32| {
        ratchet_state_bytes(
            &dhs,
            Some(&dhr),
            &rk,
            Some(&cks),
            Some(&ckr),
            ns,
            nr,
            0,
            0,
            &[],
        )
    };

    let (start, mut steps) = match template % 6 {
        0 | 1 => {
            let role = (template % 6) as u8;
            let mut p = vec![role];
            p.extend_from_slice(&rng.key());
            p.extend_from_slice(&dhs);
            p.extend_from_slice(&dhr);
            p.extend_from_slice(&rng.key());
            (Start::Fresh(p), Vec::new())
        }
        2 => {
            // The classical sending counter at its ceiling: the send is
            // refused by that half and the whole call with it.
            let c = both_chains(u32::MAX, 0);
            let s = sparse_state_bytes(&rk, 0, 0x00, Some((&cks, 0)), Some((&ckr, 0)), &[]);
            (
                Start::Stored(triple_state_bytes(&c, &s)),
                vec![TStep::Send {
                    epoch: 0,
                    out: None,
                }],
            )
        }
        3 => {
            // The sparse sending chain at its ceiling, with the classical
            // half one below its own, so the refusal is the sparse half's.
            let c = both_chains(u32::MAX - 1, 0);
            let s = sparse_state_bytes(&rk, 0, 0x00, Some((&cks, u64::MAX)), Some((&ckr, 0)), &[]);
            (
                Start::Stored(triple_state_bytes(&c, &s)),
                vec![TStep::Send {
                    epoch: 0,
                    out: None,
                }],
            )
        }
        4 => {
            // The sparse epoch one below its reserved value: the advance onto
            // `u64::MAX` is refused inside the sparse half.
            let e = u64::MAX - 1;
            let c = both_chains(0, 0);
            let s = sparse_state_bytes(&rk, e, 0x00, Some((&cks, 0)), Some((&ckr, 0)), &[]);
            (
                Start::Stored(triple_state_bytes(&c, &s)),
                vec![TStep::Receive {
                    dh: dhr,
                    pn: 0,
                    n: 0,
                    dh_recv: rng.key(),
                    dh_send: rng.key(),
                    new_pub: rng.canonical_key(),
                    epoch: e,
                    pq_n: 1,
                    out: Some((u64::MAX, rng.key())),
                }],
            )
        }
        _ => {
            let c = both_chains(0, 0);
            let s = sparse_state_bytes(&rk, 0, 0x00, Some((&cks, 0)), Some((&ckr, 0)), &[]);
            (Start::Stored(triple_state_bytes(&c, &s)), Vec::new())
        }
    };

    let mut shadow_n = 0u32;
    let mut shadow_pq = 0u64;
    let mut epoch = 0u64;
    while steps.len() < STEPS {
        if rng.below(10) < 4 {
            let out = match rng.below(10) {
                0..=1 => Some((epoch.saturating_add(1), rng.key())),
                _ => None,
            };
            if out.is_some() {
                epoch = epoch.saturating_add(1);
                shadow_pq = 0;
            }
            steps.push(TStep::Send { epoch, out });
            shadow_pq = shadow_pq.saturating_add(1);
            continue;
        }
        let out = match rng.below(10) {
            0 => Some((epoch.saturating_add(1), rng.key())),
            1 => Some((epoch.saturating_add(2), rng.key())),
            _ => None,
        };
        let named = match out {
            Some((e, _)) => e,
            None => epoch,
        };
        let n = match rng.below(10) {
            0..=5 => shadow_n,
            6..=7 => shadow_n.saturating_add(1 + rng.below(u64::from(GATE_SKIP)) as u32),
            _ => shadow_n.saturating_add(MAX_SKIP + 1),
        };
        let pq_n = match rng.below(10) {
            0..=5 => shadow_pq.saturating_add(1),
            6..=7 => shadow_pq.saturating_add(1 + rng.below(u64::from(GATE_SKIP))),
            _ => shadow_pq.saturating_add(u64::from(MAX_SKIP) + 2),
        };
        steps.push(TStep::Receive {
            dh: dhr,
            pn: 0,
            n,
            dh_recv: rng.key(),
            dh_send: rng.key(),
            new_pub: rng.canonical_key(),
            epoch: named,
            pq_n,
            out,
        });
        if out.is_some() {
            epoch = named;
            shadow_pq = 0;
        }
        if n >= shadow_n {
            shadow_n = n.saturating_add(1);
        }
        if pq_n > shadow_pq {
            shadow_pq = pq_n;
        }
    }

    TripleSequence { start, steps }
}

// --- The Braid -------------------------------------------------------------

/// A persisted erasure encoder, from the layout in
/// `session-persistence.md`, Erasure coder sub-formats, sized for a value of
/// `value_len` bytes.
fn encoder_bytes(value_len: usize, next: u16, fill: u8) -> Vec<u8> {
    let chunks = value_len.div_ceil(32);
    let mut out = Vec::new();
    out.extend_from_slice(&next.to_be_bytes());
    out.push(0x00);
    out.extend_from_slice(&(chunks as u32).to_be_bytes());
    for i in 0..chunks {
        out.extend_from_slice(&[fill.wrapping_add(i as u8); 32]);
    }
    out
}

/// A persisted erasure decoder sized for `value_len` bytes, holding the
/// codewords at `held`.
fn decoder_bytes(value_len: usize, held: &[(u16, u8)]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&(value_len as u64).to_be_bytes());
    out.extend_from_slice(&(value_len.div_ceil(32) as u64).to_be_bytes());
    out.extend_from_slice(&(held.len() as u32).to_be_bytes());
    for (i, f) in held {
        out.extend_from_slice(&i.to_be_bytes());
        out.extend_from_slice(&[*f; 32]);
    }
    out
}

/// A stored Braid state, assembled from the layout in
/// `session-persistence.md`, Braid, rather than by either implementation.
fn braid_state_bytes(tag: u8, epoch: u64, auth: &[u8; 64], fields: &[Vec<u8>]) -> Vec<u8> {
    let mut out = vec![0x01, tag];
    if tag == 11 {
        return out;
    }
    out.extend_from_slice(&epoch.to_be_bytes());
    out.extend_from_slice(auth);
    for f in fields {
        out.extend_from_slice(&(f.len() as u32).to_be_bytes());
        out.extend_from_slice(f);
    }
    out
}

fn braid_kind(e: tacenta_braid::BraidDecodeError) -> &'static str {
    use tacenta_braid::BraidDecodeError as E;
    match e {
        E::UnknownVersion => "wrong-version",
        E::TooShort | E::Malformed => "short-or-malformed",
    }
}

/// Every Braid state this file can assemble, by tag.
///
/// Tags 1 to 4 carry a `key_pair`, whose `header` and `ek_vector` the page has
/// the reader validate and whose layout it delegates to `libcrux-ml-kem`
/// (ADR-0006, point 5). Neither this file nor `tacenta-model` can build one
/// that passes, so those tags appear here only at a length both readers
/// refuse. Tags 7 to 9 carry an `encaps`, which the page has the reader check
/// for its length and nothing else, so those are built in full.
fn braid_states(rng: &mut Rng) -> Vec<(u8, Vec<u8>)> {
    let mut auth = [0u8; 64];
    for b in auth.iter_mut() {
        *b = rng.byte();
    }
    let header = vec![0xa1u8; HEADER_LEN];
    let ct1 = vec![0xc1u8; CT1_LEN];
    let ek_vector = vec![0xe4u8; EK_VECTOR_LEN];
    let encaps = vec![0x5eu8; ENCAPS_LEN];
    let hdr_value = HEADER_LEN + MAC_LEN;
    let ct2_value = CT2_LEN + MAC_LEN;
    vec![
        (0, braid_state_bytes(0, 1, &auth, &[])),
        (5, braid_state_bytes(5, 1, &auth, &[decoder_bytes(hdr_value, &[])])),
        (
            6,
            braid_state_bytes(
                6,
                2,
                &auth,
                &[header.clone(), decoder_bytes(EK_VECTOR_LEN, &[(0, 0x11)])],
            ),
        ),
        (
            7,
            braid_state_bytes(
                7,
                1,
                &auth,
                &[
                    header.clone(),
                    encaps.clone(),
                    ct1.clone(),
                    encoder_bytes(CT1_LEN, 3, 0x20),
                    decoder_bytes(EK_VECTOR_LEN, &[]),
                ],
            ),
        ),
        (
            8,
            braid_state_bytes(
                8,
                3,
                &auth,
                &[
                    encaps.clone(),
                    ct1.clone(),
                    ek_vector,
                    encoder_bytes(CT1_LEN, 0, 0x30),
                ],
            ),
        ),
        (
            9,
            braid_state_bytes(
                9,
                1,
                &auth,
                &[
                    header,
                    encaps,
                    ct1,
                    decoder_bytes(EK_VECTOR_LEN, &[(2, 0x44), (5, 0x55)]),
                ],
            ),
        ),
        (
            10,
            braid_state_bytes(10, 1, &auth, &[encoder_bytes(ct2_value, 2, 0x40)]),
        ),
        (11, braid_state_bytes(11, 0, &auth, &[])),
        // A key pair at a length both readers refuse: the part of the
        // key-pair rule that does not need the delegated layout.
        (
            1,
            braid_state_bytes(
                1,
                1,
                &auth,
                &[
                    vec![0x4bu8; KEY_PAIR_LEN - 1],
                    encoder_bytes(hdr_value, 1, 0x50),
                ],
            ),
        ),
        // The two ends of the epoch's range, both of which the rules put
        // outside it: a live state at epoch 0, and one at the reserved
        // `u64::MAX`. Both readers refuse each, and a model that stopped
        // refusing either would be caught here rather than only by the
        // vectors. Corrupting a byte of a live state reaches neither, which
        // is why they are built rather than left to `corrupt`.
        (0, braid_state_bytes(0, 0, &auth, &[])),
        (0, braid_state_bytes(0, u64::MAX, &auth, &[])),
    ]
}

/// The Braid's `Ct2Sampled` steps: a message at the next epoch takes
/// transition (13), and at `u64::MAX - 1` the same message fails instead,
/// because the step would land on the reserved epoch.
fn braid_step_bytes(epoch: u64) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&epoch.to_be_bytes());
    out.push(0x00); // type None
    out.push(0x00); // no codeword
    out.extend_from_slice(&0u16.to_be_bytes());
    out.extend_from_slice(&[0u8; 32]);
    out
}

fn braid_readback(bytes: &[u8]) -> String {
    match tacenta_braid::Braid::from_bytes(bytes) {
        Ok(b) => {
            if b.to_bytes().as_slice() == bytes {
                "same".to_string()
            } else {
                "differs".to_string()
            }
        }
        Err(e) => format!("refused:{}", braid_kind(e)),
    }
}

/// One `run braid stored` sequence against the model's answer.
fn check_braid(
    start: &[u8],
    steps: &[u64],
    answer: &[String],
    seen: &mut Observed,
) -> Result<(), String> {
    use tacenta_braid::{Braid, Msg, MsgType};

    let mut lines = answer.iter();
    let first = lines.next().ok_or("the model answered nothing")?;
    let want = parse_start(first)?;

    let mut braid = match (Braid::from_bytes(start), want) {
        (Ok(b), ModelStart::Ok { bytes: want, .. }) => {
            let got = b.to_bytes();
            if got.as_slice() != want {
                return Err(format!(
                    "the stored start: the crate reads it back as {}, the model as {}",
                    hex::encode(got.as_slice()),
                    hex::encode(&want)
                ));
            }
            b
        }
        (Err(e), ModelStart::Refused(kind)) => {
            let mine = braid_kind(e);
            if !refusals_agree(start, BRAID_FIXED_LEN, &kind, mine) {
                return Err(format!(
                    "the stored start: the crate refuses it as {mine}, the model as {kind}"
                ));
            }
            return Ok(());
        }
        (Ok(_), ModelStart::Refused(kind)) => {
            return Err(format!(
                "the stored start: the model refuses it as {kind}, the crate accepts it"
            ));
        }
        (Err(e), ModelStart::Ok { .. }) => {
            return Err(format!(
                "the stored start: the crate refuses it ({e:?}), the model accepts it"
            ));
        }
    };

    for (i, epoch) in steps.iter().enumerate() {
        let line = lines
            .next()
            .ok_or_else(|| format!("step {}: the model answered nothing", i + 1))?;
        let want = parse_step(line)?;
        let msg = Msg {
            epoch: *epoch,
            ty: MsgType::None,
            data: None,
        };
        let (_e, _out, next) = braid.receive(&msg);
        braid.commit(next);
        seen.steps += 1;
        seen.braid_steps += 1;
        if braid.failed() {
            seen.braid_ceiling_failed += 1;
        } else if braid.state_tag() == 0 {
            seen.braid_ceiling_stepped += 1;
        }
        match want {
            // The Braid's receive refuses nothing: it answers with a state,
            // `Failed` among them, so every step is an `ok` on both sides and
            // the epoch ceiling shows up in the bytes.
            ModelStep::Ok { bytes, readback } => {
                compare_state(i + 1, braid.to_bytes().as_slice(), &bytes, &readback, &{
                    braid_readback(braid.to_bytes().as_slice())
                })?;
            }
            ModelStep::Refused { .. } => {
                return Err(format!(
                    "step {}: the model refuses it, and the Braid's receive refuses nothing",
                    i + 1
                ));
            }
        }
    }
    Ok(())
}

/// The two composed formats, in one round: the Triple Ratchet through
/// generated operation sequences, and the Braid through generated stored
/// states, the two `Ct2Sampled` transitions, and corrupted imports of both.
fn check_composed(exe: &Path, seed: u64, sequences: usize, long: bool, seen: &mut Observed) {
    let mut requests = Vec::new();
    let mut triples: Vec<(usize, TripleSequence)> = Vec::new();
    for i in 0..sequences {
        let mut rng = Rng::new(seed ^ (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15));
        let t = generate_triple(&mut rng, i, long);
        requests.push(t.start.request("triple", &encode_triple(&t.steps)));
        triples.push((requests.len() - 1, t));
    }

    // The Braid, by tag, and the two ceiling steps.
    let mut rng = Rng::new(seed ^ 0x0b0b_0b0b_0b0b_0b0b);
    let states = braid_states(&mut rng);
    let mut braid_reads: Vec<Vec<u8>> = Vec::new();
    for (_tag, bytes) in &states {
        braid_reads.push(bytes.clone());
        for c in corrupt(&mut rng, bytes) {
            braid_reads.push(c);
        }
    }
    let read_first = requests.len();
    for b in &braid_reads {
        requests.push(format!("read braid {}", hex::encode(b)));
    }

    let mut auth = [0u8; 64];
    for b in auth.iter_mut() {
        *b = rng.byte();
    }
    let ct2_value = CT2_LEN + MAC_LEN;
    let ceiling_runs: Vec<(Vec<u8>, Vec<u64>)> = vec![
        // Below the reserved epoch: transition (13).
        (
            braid_state_bytes(10, 1, &auth, &[encoder_bytes(ct2_value, 1, 0x60)]),
            vec![2],
        ),
        (
            braid_state_bytes(
                10,
                u64::MAX - 2,
                &auth,
                &[encoder_bytes(ct2_value, 1, 0x61)],
            ),
            vec![u64::MAX - 1],
        ),
        // At it: the step would land on `u64::MAX`, so the Braid fails.
        (
            braid_state_bytes(
                10,
                u64::MAX - 1,
                &auth,
                &[encoder_bytes(ct2_value, 1, 0x62)],
            ),
            vec![u64::MAX],
        ),
    ];
    let run_first = requests.len();
    for (start, steps) in &ceiling_runs {
        let mut encoded = Vec::new();
        for e in steps {
            encoded.extend_from_slice(&braid_step_bytes(*e));
        }
        requests.push(format!(
            "run braid stored {} {}",
            hex::encode(start),
            hex::encode(&encoded)
        ));
    }

    let answers = ask_model(exe, &requests);

    for (at, t) in &triples {
        if let Err(e) = check_triple(&t.start, &t.steps, &answers[*at], seen) {
            let (minimal, message) = shrink(&t.steps, &mut |steps: &[TStep]| {
                let request = t.start.request("triple", &encode_triple(steps));
                let a = ask_model(exe, std::slice::from_ref(&request));
                let mut s = Observed::default();
                check_triple(&t.start, steps, &a[0], &mut s)
            });
            panic!(
                "\n\ntacenta-model and tacenta-core disagree on the Triple Ratchet.\n\
                 seed: {seed} ({seed:#x})\n\
                 first report: {e}\n\
                 minimal: {message}\n\
                 request: {}\n\n",
                t.start.request("triple", &encode_triple(&minimal))
            );
        }
    }

    for (i, bytes) in braid_reads.iter().enumerate() {
        let answer = &answers[read_first + i];
        let line = answer.first().expect("a read answer");
        seen.braid_reads += 1;
        let model = parse_read(line).expect("a read line");
        let rust = tacenta_braid::Braid::from_bytes(bytes)
            .map(|b| b.to_bytes().to_vec())
            .map_err(braid_kind);
        match (model, rust) {
            (Some(want), Ok(got)) => {
                seen.braid_reads_accepted += 1;
                assert_eq!(
                    hex::encode(&got),
                    hex::encode(&want),
                    "\n\ntacenta-model and tacenta-core disagree on an imported Braid.\n\
                     seed: {seed} ({seed:#x})\n\
                     request: read braid {}\n\n",
                    hex::encode(bytes)
                );
            }
            (None, Err(mine)) => {
                let kind = read_refusal(line).expect("the model's refusal");
                assert!(
                    refusals_agree(bytes, BRAID_FIXED_LEN, &kind, mine),
                    "\n\ntacenta-model and tacenta-core disagree on why a Braid import is \
                     refused.\nseed: {seed} ({seed:#x})\n\
                     the model says {kind}, the crate {mine}\n\
                     request: read braid {}\n\n",
                    hex::encode(bytes)
                );
            }
            (Some(_), Err(mine)) => panic!(
                "\n\ntacenta-model accepts a Braid tacenta-core refuses ({mine}).\n\
                 seed: {seed} ({seed:#x})\n\
                 request: read braid {}\n\n",
                hex::encode(bytes)
            ),
            (None, Ok(_)) => panic!(
                "\n\ntacenta-core accepts a Braid tacenta-model refuses.\n\
                 seed: {seed} ({seed:#x})\n\
                 request: read braid {}\n\n",
                hex::encode(bytes)
            ),
        }
    }

    for (i, (start, steps)) in ceiling_runs.iter().enumerate() {
        if let Err(e) = check_braid(start, steps, &answers[run_first + i], seen) {
            panic!(
                "\n\ntacenta-model and tacenta-core disagree on the Braid.\n\
                 seed: {seed} ({seed:#x})\n\
                 {e}\n\
                 start: {}\n\n",
                hex::encode(start)
            );
        }
    }

    // The corrupted imports of the states the Triple Ratchet sequences
    // reached, read by both sides.
    let mut requests = Vec::new();
    let mut which: Vec<Vec<u8>> = Vec::new();
    for (at, _) in &triples {
        let Some(last) = answers[*at].last() else {
            continue;
        };
        let bytes = match parse_step(last).or_else(|_| {
            parse_start(last).map(|s| match s {
                ModelStart::Ok { bytes, readback } => ModelStep::Ok { bytes, readback },
                ModelStart::Refused(k) => ModelStep::Refused {
                    ceiling: false,
                    bytes: Vec::new(),
                    readback: k,
                },
            })
        }) {
            Ok(ModelStep::Ok { bytes, .. }) | Ok(ModelStep::Refused { bytes, .. }) => bytes,
            Err(_) => continue,
        };
        for c in corrupt(&mut rng, &bytes) {
            requests.push(format!("read triple {}", hex::encode(&c)));
            which.push(c);
        }
    }
    if requests.is_empty() {
        return;
    }
    let read_answers = ask_model(exe, &requests);
    for (bytes, answer) in which.iter().zip(read_answers.iter()) {
        let line = answer.first().expect("a read answer");
        seen.triple_reads += 1;
        let model = parse_read(line).expect("a read line");
        let rust = tacenta_triple::State::from_bytes(bytes)
            .map(|s| s.to_bytes().to_vec())
            .map_err(triple_kind);
        match (model, rust) {
            (Some(want), Ok(got)) => {
                seen.triple_reads_accepted += 1;
                assert_eq!(
                    hex::encode(&got),
                    hex::encode(&want),
                    "\n\ntacenta-model and tacenta-core disagree on an imported Triple \
                     Ratchet state.\nseed: {seed} ({seed:#x})\n\
                     request: read triple {}\n\n",
                    hex::encode(bytes)
                );
            }
            (None, Err(mine)) => {
                let kind = read_refusal(line).expect("the model's refusal");
                assert!(
                    refusals_agree(bytes, TRIPLE_FIXED_LEN, &kind, mine),
                    "\n\ntacenta-model and tacenta-core disagree on why a Triple Ratchet \
                     import is refused.\nseed: {seed} ({seed:#x})\n\
                     the model says {kind}, the crate {mine}\n\
                     request: read triple {}\n\n",
                    hex::encode(bytes)
                );
            }
            (Some(_), Err(mine)) => panic!(
                "\n\ntacenta-model accepts a Triple Ratchet state tacenta-core refuses \
                 ({mine}).\nseed: {seed} ({seed:#x})\n\
                 request: read triple {}\n\n",
                hex::encode(bytes)
            ),
            (None, Ok(_)) => panic!(
                "\n\ntacenta-core accepts a Triple Ratchet state tacenta-model refuses.\n\
                 seed: {seed} ({seed:#x})\n\
                 request: read triple {}\n\n",
                hex::encode(bytes)
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// The test
// ---------------------------------------------------------------------------

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

/// Every request for one round, and enough to check the answers against.
struct Round {
    requests: Vec<String>,
    ratchet: Vec<(usize, RatchetSequence)>,
    sparse: Vec<(usize, SparseSequence)>,
}

fn build_round(seed: u64, sequences: usize, long: bool) -> Round {
    let mut requests = Vec::new();
    let mut ratchet = Vec::new();
    let mut sparse = Vec::new();
    for i in 0..sequences {
        // One stream per sequence, so a sequence means the same thing whatever
        // the ones before it did and a failing one can be rerun on its own.
        let mut rng = Rng::new(seed ^ (i as u64).wrapping_mul(0x2545_f491_4f6c_dd1d));
        let r = generate_ratchet(&mut rng, i, long);
        requests.push(r.start.request("ratchet", &encode_ratchet(&r.steps)));
        ratchet.push((requests.len() - 1, r));

        let s = generate_sparse(&mut rng, i, long);
        requests.push(s.start.request("sparse", &encode_sparse(&s.steps)));
        sparse.push((requests.len() - 1, s));
    }
    Round {
        requests,
        ratchet,
        sparse,
    }
}

/// Rerun one classical sequence on its own: used while shrinking, where each
/// candidate is a fresh pair of runs.
fn run_ratchet_once(exe: &Path, start: &Start, steps: &[RStep]) -> Result<(), String> {
    let request = start.request("ratchet", &encode_ratchet(steps));
    let answers = ask_model(exe, std::slice::from_ref(&request));
    let mut seen = Observed::default();
    check_ratchet(start, steps, &answers[0], &mut seen)
}

fn run_sparse_once(exe: &Path, start: &Start, steps: &[SStep]) -> Result<(), String> {
    let request = start.request("sparse", &encode_sparse(steps));
    let answers = ask_model(exe, std::slice::from_ref(&request));
    let mut seen = Observed::default();
    check_sparse(start, steps, &answers[0], &mut seen)
}

/// The shortest prefix, then the shortest subsequence, that still disagrees.
/// Greedy and bounded: a minimal sequence a person can read is the point, not
/// a provably minimal one.
fn shrink<S: Clone>(
    steps: &[S],
    run: &mut dyn FnMut(&[S]) -> Result<(), String>,
) -> (Vec<S>, String) {
    let mut best: Vec<S> = steps.to_vec();
    let mut message = run(&best).err().unwrap_or_default();
    // Prefixes first: most disagreements are at one step and everything after
    // it is noise.
    for cut in 1..=best.len() {
        let candidate = &best[..cut];
        if let Err(e) = run(candidate) {
            best = candidate.to_vec();
            message = e;
            break;
        }
    }
    // Then drop single steps, last first, keeping anything that still fails.
    let mut i = best.len();
    while i > 0 {
        i -= 1;
        if best.len() <= 1 {
            break;
        }
        let mut candidate = best.clone();
        candidate.remove(i);
        if let Err(e) = run(&candidate) {
            best = candidate;
            message = e;
        }
    }
    (best, message)
}

#[test]
fn the_model_and_the_core_agree_on_generated_sequences() {
    let Some(exe) = difftest_path() else {
        // A gate that cannot run must not report green where it is meant to
        // run. `tooling/ci.sh` sets the variable after building the model, and
        // the workflow's vectors job installs Lean, so both fail here; a Rust
        // toolchain on its own skips and says how to build the model.
        if std::env::var("GITHUB_ACTIONS").as_deref() == Ok("true")
            || std::env::var("TACENTA_DIFFTEST_REQUIRED").is_ok()
        {
            panic!(
                "the model's difftest executable is missing. Build it with \
                 '(cd tacenta-model && lake build difftest)', or name it in \
                 TACENTA_DIFFTEST."
            );
        }
        eprintln!(
            "differential: no model executable, skipping. Build it with \
             '(cd tacenta-model && lake build difftest)'."
        );
        return;
    };

    let seed = std::env::var("TACENTA_DIFF_SEED")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(SEED);
    let sequences = env_usize("TACENTA_DIFF_SEQUENCES", SEQUENCES);
    let long = std::env::var("TACENTA_DIFF_LONG").is_ok();
    eprintln!(
        "differential: seed {seed} ({seed:#x}), {sequences} sequences per ratchet, \
         up to {STEPS} steps each{}",
        if long { ", long run" } else { "" }
    );

    let round = build_round(seed, sequences, long);
    let answers = ask_model(&exe, &round.requests);
    let mut seen = Observed::default();

    for (at, r) in &round.ratchet {
        if let Err(e) = check_ratchet(&r.start, &r.steps, &answers[*at], &mut seen) {
            let (minimal, message) = shrink(&r.steps, &mut |steps: &[RStep]| {
                run_ratchet_once(&exe, &r.start, steps)
            });
            panic!(
                "\n\ntacenta-model and tacenta-core disagree on the classical ratchet.\n\
                 seed: {seed} ({seed:#x})\n\
                 first report: {e}\n\
                 minimal: {message}\n\
                 request: {}\n\n",
                r.start.request("ratchet", &encode_ratchet(&minimal))
            );
        }
    }
    for (at, s) in &round.sparse {
        if let Err(e) = check_sparse(&s.start, &s.steps, &answers[*at], &mut seen) {
            let (minimal, message) = shrink(&s.steps, &mut |steps: &[SStep]| {
                run_sparse_once(&exe, &s.start, steps)
            });
            panic!(
                "\n\ntacenta-model and tacenta-core disagree on the sparse ratchet.\n\
                 seed: {seed} ({seed:#x})\n\
                 first report: {e}\n\
                 minimal: {message}\n\
                 request: {}\n\n",
                s.start.request("sparse", &encode_sparse(&minimal))
            );
        }
    }

    check_imports(&exe, seed, &round, &answers, &mut seen);
    check_composed(&exe, seed, sequences, long, &mut seen);

    eprintln!(
        "differential: {} steps ({} taken, {} refused), {} Diffie-Hellman or epoch steps, \
         {} steps storing keys, {} using one, {} dropping more than one at once, \
         {} refused at a skip bound; \
         ceilings reached: ns {}, nr {}, sparse epoch {}, sparse send {}, sparse receive {}; \
         {} imports ({} accepted, {} wrong-version, {} short-or-malformed)",
        seen.steps,
        seen.accepted,
        seen.refused,
        seen.dh_steps,
        seen.keys_stored,
        seen.keys_used,
        seen.store_shrank_beyond_one,
        seen.skip_refused,
        seen.ratchet_send_ceiling,
        seen.ratchet_receive_ceiling,
        seen.sparse_epoch_ceiling,
        seen.sparse_send_ceiling,
        seen.sparse_receive_ceiling,
        seen.imports,
        seen.imports_accepted,
        seen.imports_wrong_version,
        seen.imports_malformed,
    );

    // What the run had to reach. A harness that stops reaching the ceilings,
    // the skips or the refusals fails here rather than passing on fewer.
    assert!(
        seen.accepted > 0 && seen.refused > 0,
        "took and refused steps"
    );
    assert!(seen.dh_steps > 0, "no Diffie-Hellman or epoch step");
    assert!(seen.keys_stored > 0, "no step stored a skipped key");
    assert!(seen.keys_used > 0, "no step used a stored key");
    assert!(
        seen.store_shrank_beyond_one > 0,
        "no step aged keys out of the store or retired an epoch with its keys"
    );
    assert!(seen.skip_refused > 0, "no step was refused at a skip bound");
    assert!(
        seen.ratchet_send_ceiling > 0,
        "the classical sending counter's ceiling was not reached"
    );
    assert!(
        seen.ratchet_receive_ceiling > 0,
        "the classical receiving counter's ceiling was not reached"
    );
    assert!(
        seen.sparse_epoch_ceiling > 0,
        "the sparse epoch's ceiling was not reached"
    );
    assert!(
        seen.sparse_send_ceiling > 0,
        "the sparse sending counter's ceiling was not reached"
    );
    assert!(
        seen.sparse_receive_ceiling > 0,
        "the sparse receiving counter's ceiling was not reached"
    );
    assert!(
        seen.imports_accepted > 0 && seen.imports_wrong_version > 0 && seen.imports_malformed > 0,
        "the corrupted imports reached every verdict"
    );

    eprintln!(
        "differential: the composed formats: {} Triple Ratchet steps ({} refused at a half's \
         ceiling), {} Triple Ratchet imports ({} accepted); {} Braid imports ({} accepted), \
         {} Braid steps ({} taking transition 13, {} failing at the reserved epoch)",
        seen.triple_steps,
        seen.triple_ceiling,
        seen.triple_reads,
        seen.triple_reads_accepted,
        seen.braid_reads,
        seen.braid_reads_accepted,
        seen.braid_steps,
        seen.braid_ceiling_stepped,
        seen.braid_ceiling_failed,
    );

    // What the composed half had to reach, on the same principle as above: a
    // run that stopped reaching these fails here rather than passing on fewer.
    assert!(seen.triple_steps > 0, "no Triple Ratchet step ran");
    assert!(
        seen.triple_ceiling > 0,
        "no Triple Ratchet step was refused at one of its halves' ceilings"
    );
    assert!(
        seen.triple_reads_accepted > 0,
        "no corrupted Triple Ratchet import was accepted by both sides"
    );
    assert!(
        seen.braid_reads_accepted > 0,
        "no generated Braid state was accepted by both sides"
    );
    assert!(
        seen.braid_ceiling_stepped > 0,
        "the Braid's transition (13) was not reached"
    );
    assert!(
        seen.braid_ceiling_failed > 0,
        "the Braid's refusal at the reserved epoch was not reached"
    );
}

/// The corrupted-byte imports: every state the model wrote, changed one way,
/// given to both readers.
fn check_imports(
    exe: &Path,
    seed: u64,
    round: &Round,
    answers: &[Vec<String>],
    seen: &mut Observed,
) {
    let mut requests = Vec::new();
    // `true` for the classical reader.
    let mut which: Vec<(bool, Vec<u8>)> = Vec::new();
    let mut rng = Rng::new(seed ^ 0x1234_5678_9abc_def0);

    for (classical, list) in [
        (true, &round.ratchet.iter().map(|p| p.0).collect::<Vec<_>>()),
        (false, &round.sparse.iter().map(|p| p.0).collect::<Vec<_>>()),
    ] {
        for at in list.iter() {
            // The state after the last step the model reported, which is the
            // deepest state the sequence reached.
            let Some(last) = answers[*at].last() else {
                continue;
            };
            let bytes = match parse_step(last).or_else(|_| {
                parse_start(last).map(|s| match s {
                    ModelStart::Ok { bytes, readback } => ModelStep::Ok { bytes, readback },
                    ModelStart::Refused(k) => ModelStep::Refused {
                        ceiling: false,
                        bytes: Vec::new(),
                        readback: k,
                    },
                })
            }) {
                Ok(ModelStep::Ok { bytes, .. }) | Ok(ModelStep::Refused { bytes, .. }) => bytes,
                Err(_) => continue,
            };
            for c in corrupt(&mut rng, &bytes) {
                requests.push(format!(
                    "read {} {}",
                    if classical { "ratchet" } else { "sparse" },
                    hex::encode(&c)
                ));
                which.push((classical, c));
            }
        }
    }
    if requests.is_empty() {
        return;
    }
    let read_answers = ask_model(exe, &requests);
    for ((classical, bytes), answer) in which.iter().zip(read_answers.iter()) {
        let line = answer.first().expect("a read answer");
        seen.imports += 1;
        let model = parse_read(line).expect("a read line");
        let (fixed, rust): (usize, Result<Vec<u8>, &'static str>) = if *classical {
            (
                RATCHET_FIXED_LEN,
                ratchet::State::from_bytes(bytes)
                    .map(|s| s.to_bytes().to_vec())
                    .map_err(ratchet_kind),
            )
        } else {
            (
                SPARSE_FIXED_PREFIX,
                tacenta_spqr::State::from_bytes(bytes)
                    .map(|s| s.to_bytes().to_vec())
                    .map_err(sparse_kind),
            )
        };
        match (model, rust) {
            (Some(want), Ok(got)) => {
                seen.imports_accepted += 1;
                assert_eq!(
                    hex::encode(&got),
                    hex::encode(&want),
                    "\n\ntacenta-model and tacenta-core disagree on an imported state.\n\
                     seed: {seed} ({seed:#x})\n\
                     request: read {} {}\n\n",
                    if *classical { "ratchet" } else { "sparse" },
                    hex::encode(bytes)
                );
            }
            (None, Err(mine)) => {
                let kind = read_refusal(line).expect("the model's refusal");
                if kind == "wrong-version" {
                    seen.imports_wrong_version += 1;
                } else {
                    seen.imports_malformed += 1;
                }
                assert!(
                    refusals_agree(bytes, fixed, &kind, mine),
                    "\n\ntacenta-model and tacenta-core disagree on why an import is refused.\n\
                     seed: {seed} ({seed:#x})\n\
                     the model says {kind}, the crate {mine}\n\
                     request: read {} {}\n\n",
                    if *classical { "ratchet" } else { "sparse" },
                    hex::encode(bytes)
                );
            }
            (Some(_), Err(mine)) => panic!(
                "\n\ntacenta-model accepts an imported state tacenta-core refuses ({mine}).\n\
                 seed: {seed} ({seed:#x})\n\
                 request: read {} {}\n\n",
                if *classical { "ratchet" } else { "sparse" },
                hex::encode(bytes)
            ),
            (None, Ok(_)) => panic!(
                "\n\ntacenta-core accepts an imported state tacenta-model refuses.\n\
                 seed: {seed} ({seed:#x})\n\
                 request: read {} {}\n\n",
                if *classical { "ratchet" } else { "sparse" },
                hex::encode(bytes)
            ),
        }
    }
}
