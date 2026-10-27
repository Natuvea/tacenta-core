//! The entry of the `frame_size_boundary` fuzz target, kept outside `fuzz_targets/` so that
//! `tacenta-core/tests/fuzz_frame_size_seeds.rs` can run the committed seed corpus through the same function
//! with an ordinary `cargo test`. Test and fuzz code only; nothing here is in a shipping crate.
//!
//! **What it reaches.** The size rule (tacenta-spec/protocol/message-format.md, Message size) has its edges at
//! `MAX_RATCHET_FRAME_LEN` = 1,048,710 and `MAX_INITIAL_FRAME_LEN` = 1,050,362 bytes, far past the 4,096-byte
//! inputs the fast campaign uses. An input here is therefore a short description of a frame, expanded before
//! it is received, so a seed of a few dozen bytes stands for a frame of a megabyte and libFuzzer's mutations of
//! the description move the frame's length, its first bytes and its declared KEM length across the edges:
//!
//! * mode `0`: the frame is the rest of the input, as it is (with `-max_len` above 1,050,363 a raw campaign can
//!   reach the outer bound too, slowly);
//! * mode `1`: four bytes of length (big-endian, taken modulo `CAP + 1`), one fill byte, then a prefix; the
//!   frame is the prefix followed by the fill byte up to the length, the layout of
//!   `tacenta-test-vectors/vectors/serialization/frame-size.json` with a chosen fill;
//! * mode `2`: four bytes of declared KEM-ciphertext length (modulo 70,001) and four bytes of inner length
//!   (modulo `CAP + 1`); the frame is the fixture's genuine repeated initial message re-wrapped with a zero
//!   `kem_ciphertext` of the declared length around its own ratchet message padded with zeros to the inner
//!   length, which is what an attacker on the wire can do to a repeat.
//!
//! **What it asserts.** Each frame goes to `Session::decrypt` on a responder session and to
//! `establish_responder` on a prekey store, both restored from fixed bytes. The harness computes the size rule
//! itself from the frame's length, first two bytes and bytes 68 to 71, in `u128`, and requires: a frame the
//! rule refuses is refused by both as `Decode(TooLong)`, with no call to the random source and the session and
//! store bytes unchanged; a frame it admits is refused by neither as too long. Either failing is a panic, so
//! the fuzzer reports it.
//!
//! **What it reports.** [`run`] returns, for each entry, the branch the frame took, read from the result and
//! the frame's own lengths, never from a counter in the library: `OuterTooLong` (refused, longer than
//! `MAX_INITIAL_FRAME_LEN`), `NestedTooLong` (an initial frame within it, refused because its located ratchet
//! message is too long), `RatchetTooLong` (a frame that is not an initial frame, within the outer bound,
//! refused), `AtLimitToDecoder` (exactly at a bound, admitted, and refused or accepted by what follows), and
//! `WithinBoundsMalformed` (under the bounds and refused as some other decode failure). Everything else is
//! `Other`.

use std::sync::OnceLock;

use rand_core::{CryptoRng, RngCore};
use tacenta_core::serialization::{
    DecodeError, MAX_INITIAL_FRAME_LEN, MAX_RATCHET_FRAME_LEN, decode_initial, encode_initial,
};
use tacenta_core::sessions::{
    Expectation, Identity, LifecycleError, PrekeyStore, Session, establish_initiator,
    establish_responder,
};

/// The longest frame modes 1 and 2 build: past the outer bound by more than one padding block.
pub const CAP: usize = MAX_INITIAL_FRAME_LEN + 64;

/// The branch one receiving entry took for a frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Branch {
    OuterTooLong,
    NestedTooLong,
    RatchetTooLong,
    AtLimitToDecoder,
    WithinBoundsMalformed,
    Other,
}

impl Branch {
    pub fn name(self) -> &'static str {
        match self {
            Branch::OuterTooLong => "outer-too-long",
            Branch::NestedTooLong => "nested-too-long",
            Branch::RatchetTooLong => "ratchet-too-long",
            Branch::AtLimitToDecoder => "at-limit-to-decoder",
            Branch::WithinBoundsMalformed => "within-bounds-malformed",
            Branch::Other => "other",
        }
    }
}

/// The branches the session's decrypt and responder establishment took.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Report {
    pub session: Branch,
    pub responder: Branch,
}

/// A deterministic stream that counts the calls made to it. Not random; a fixture source.
struct Stream {
    state: u64,
    calls: usize,
}

impl Stream {
    fn new(seed: u64) -> Stream {
        Stream {
            state: seed,
            calls: 0,
        }
    }
    fn word(&mut self) -> u64 {
        // splitmix64
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

impl RngCore for Stream {
    fn next_u32(&mut self) -> u32 {
        self.calls += 1;
        self.word() as u32
    }
    fn next_u64(&mut self) -> u64 {
        self.calls += 1;
        self.word()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.calls += 1;
        for chunk in dest.chunks_mut(8) {
            let w = self.word().to_le_bytes();
            chunk.copy_from_slice(&w[..chunk.len()]);
        }
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

// A fixture source, as the comment on `Stream` says.
impl CryptoRng for Stream {}

struct Fixture {
    identity: [u8; 32],
    store: Vec<u8>,
    session: Vec<u8>,
    /// Alice's repeat of her initial message, which Bob's session accepts as a repeat.
    repeat: Vec<u8>,
}

/// Bob's responder session, established from Alice's first initial message, the store it left, and Alice's
/// repeat, built once.
fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let mut r = Stream::new(0x6672_616d_6573);
        let alice = Identity::generate(&mut r);
        let bob = Identity::generate(&mut r);
        let mut store = bob.create_prekeys(2, &mut r);
        let bundle = store.publish();
        let mut pending =
            establish_initiator(&alice, &bundle, &Expectation::first_contact(&[]), &mut r)
                .expect("fixture: establish the initiator");
        let first = pending
            .encrypt(b"first", &mut r)
            .expect("fixture: first message");
        let (session, _) = establish_responder(&bob, &mut store, &first, &mut r)
            .expect("fixture: establish the responder");
        let repeat = pending
            .encrypt(b"repeat", &mut r)
            .expect("fixture: the repeat");
        Fixture {
            identity: *bob.export(),
            store: store.to_bytes().to_vec(),
            session: session.export().to_vec(),
            repeat,
        }
    })
}

fn be32(bytes: &[u8]) -> Option<u32> {
    Some(u32::from_be_bytes(bytes.get(..4)?.try_into().ok()?))
}

/// The frame an input describes (module documentation), or none for an input too short to describe one.
pub fn frame_of(data: &[u8]) -> Option<Vec<u8>> {
    let (&mode, rest) = data.split_first()?;
    match mode % 3 {
        0 => Some(rest.to_vec()),
        1 => {
            let length = be32(rest)? as usize % (CAP + 1);
            let fill = *rest.get(4)?;
            let prefix = rest.get(5..)?;
            let mut frame = vec![fill; length];
            let n = prefix.len().min(length);
            frame[..n].copy_from_slice(&prefix[..n]);
            Some(frame)
        }
        _ => {
            let kem_len = be32(rest)? as usize % 70_001;
            let inner_len = be32(rest.get(4..)?)? as usize % (CAP + 1);
            let d = decode_initial(&fixture().repeat).expect("the fixture's repeat decodes");
            let mut inner = d.message;
            inner.resize(inner_len, 0);
            Some(encode_initial(
                &d.identity,
                &d.ephemeral,
                &vec![0u8; kem_len],
                d.signed_prekey_id,
                d.one_time_prekey_id,
                d.kem_prekey_id,
                &inner,
            ))
        }
    }
}

/// Whether the frame is an initial frame (message-format.md, Message size).
fn is_initial(frame: &[u8]) -> bool {
    frame.len() >= 2 && frame[0] == 0x01 && frame[1] == 0x02
}

/// The ratchet message's length the rule locates, computed here in `u128` rather than by the library.
fn located_span(frame: &[u8]) -> Option<u128> {
    let len = frame.len() as u128;
    if !is_initial(frame) {
        return Some(len);
    }
    let k = u128::from(be32(frame.get(68..72)?)?);
    if 84 + k <= len {
        Some(len - 84 - k)
    } else {
        None
    }
}

/// The size rule, computed here: rule 1, then rules 2 and 3 through the located span.
fn rule_refuses(frame: &[u8]) -> bool {
    frame.len() as u128 > MAX_INITIAL_FRAME_LEN as u128
        || located_span(frame).is_some_and(|s| s > MAX_RATCHET_FRAME_LEN as u128)
}

/// Whether the frame sits exactly at a bound: the outer one, or a located ratchet message of exactly
/// `MAX_RATCHET_FRAME_LEN`.
fn at_limit(frame: &[u8]) -> bool {
    frame.len() == MAX_INITIAL_FRAME_LEN
        || located_span(frame) == Some(MAX_RATCHET_FRAME_LEN as u128)
}

const TOO_LONG: LifecycleError = LifecycleError::Decode(DecodeError::TooLong);

fn classify(frame: &[u8], result: Option<&LifecycleError>) -> Branch {
    if result == Some(&TOO_LONG) {
        if frame.len() > MAX_INITIAL_FRAME_LEN {
            Branch::OuterTooLong
        } else if is_initial(frame) {
            Branch::NestedTooLong
        } else {
            Branch::RatchetTooLong
        }
    } else if at_limit(frame) {
        Branch::AtLimitToDecoder
    } else if matches!(result, Some(LifecycleError::Decode(_))) {
        Branch::WithinBoundsMalformed
    } else {
        Branch::Other
    }
}

/// Receive `frame` on both entries, assert the size rule and the effects of its refusal, and report the
/// branches taken.
pub fn receive(frame: &[u8]) -> Report {
    let fx = fixture();
    let refuse = rule_refuses(frame);

    let mut session = Session::import(&fx.session).expect("the fixture session imports");
    let mut rng = Stream::new(1);
    let decrypted = session.decrypt(frame, &mut rng);
    let session_error = decrypted.as_ref().err();
    if refuse {
        assert_eq!(
            session_error,
            Some(&TOO_LONG),
            "decrypt: the rule refuses this frame"
        );
        assert_eq!(rng.calls, 0, "decrypt: a size refusal drew a random value");
        assert_eq!(
            session.export().as_slice(),
            fx.session.as_slice(),
            "decrypt: a size refusal changed the session"
        );
    } else {
        assert_ne!(
            session_error,
            Some(&TOO_LONG),
            "decrypt: the rule admits this frame"
        );
    }

    let mut store = PrekeyStore::from_bytes(&fx.store).expect("the fixture store reads");
    let identity = Identity::from_secret(fx.identity);
    let mut rng = Stream::new(2);
    let established = establish_responder(&identity, &mut store, frame, &mut rng);
    let responder_error = established.as_ref().err();
    if refuse {
        assert_eq!(
            responder_error,
            Some(&TOO_LONG),
            "establish_responder: the rule refuses this frame"
        );
        assert_eq!(
            rng.calls, 0,
            "establish_responder: a size refusal drew a random value"
        );
        assert_eq!(
            store.to_bytes().as_slice(),
            fx.store.as_slice(),
            "establish_responder: a size refusal changed the store"
        );
    } else {
        assert_ne!(
            responder_error,
            Some(&TOO_LONG),
            "establish_responder: the rule admits this frame"
        );
    }

    Report {
        session: classify(frame, session_error),
        responder: classify(frame, responder_error),
    }
}

/// The fuzz target's body: expand the input and receive the frame.
pub fn run(data: &[u8]) -> Option<Report> {
    let frame = frame_of(data)?;
    Some(receive(&frame))
}
