//! The size rule's vectors (`vectors/serialization/frame-size.json`; tacenta-spec/protocol/message-format.md,
//! Message size), checked against the two receiving operations that apply it.
//!
//! A vector gives a frame's `length`, four bytes big-endian, and its `prefix`; the frame is the prefix
//! followed by zero bytes up to the length (tacenta-test-vectors/README.md, Vector layouts). The runner builds
//! it and hands it to `Session::decrypt` on two sessions, a live responder session and one whose agreement has
//! failed, and to `establish_responder` on a prekey store, all rebuilt from the same stored bytes for every
//! vector.
//!
//! * An invalid vector is refused by all three as `Decode(DecodeError::TooLong)`, with the sessions' and the
//!   store's stored bytes unchanged and the random source not read; `check_frame_size` refuses it too. That
//!   is the page's precedence (Message size, Precedence): an unknown version or type byte, a malformed or
//!   unknown-prekey wrapper, and a terminal session do not change the refusal.
//! * A valid vector is admitted by `check_frame_size`, and no operation refuses it as too long; each refuses
//!   it later, for the reason it had without the rule, and changes nothing. `ratchet_span` gives the length the
//!   vector names in `fields`, and gives none when the vector leaves the field out. `decodes` says whether the
//!   decoder the session hands the frame to accepts it: when it does not, the live session and the store refuse
//!   with that decoder's own error; when it does, the live session refuses an initial frame as not its repeat,
//!   and the store refuses it at the signed-prekey lookup (the store holds no prekey these frames name, 0 or
//!   0xdeadbeef). A frame that is not an initial frame always meets the initial-message decoder's refusal on
//!   establishment. On the session whose agreement has failed the runner requires the specified order
//!   (mlkem-braid.md, Failure): `AgreementFailed` for a frame that is not an initial frame, before any decode,
//!   and for an initial frame its decoder's refusal or `NotARepeatedInitial`, with no call to the random source.

use std::sync::OnceLock;

use rand_core::{CryptoRng, RngCore};
use tacenta_core::serialization::{
    DecodeError, MessageType, check_frame_size, decode_initial, decode_message, message_type,
    ratchet_span,
};
use tacenta_core::sessions::{
    Expectation, Identity, LifecycleError, PrekeyStore, Session, establish_initiator,
    establish_responder,
};

use crate::{Vector, be32, expects_success, fields_eq, input};

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
    terminal: Vec<u8>,
}

/// A responder session established from a real initial message, the store it left, and a second responder
/// session whose agreement has failed.
fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let mut r = Stream::new(0x5153_4d45);
        let alice = Identity::generate(&mut r);
        let bob = Identity::generate(&mut r);
        let mut store = bob.create_prekeys(2, &mut r);
        let bundle = store.publish();
        let mut pending =
            establish_initiator(&alice, &bundle, &Expectation::first_contact(&[]), &mut r)
                .expect("fixture: establish the initiator");
        let first = pending
            .encrypt(b"fixture", &mut r)
            .expect("fixture: first message");
        let (session, _) = establish_responder(&bob, &mut store, &first, &mut r)
            .expect("fixture: establish the responder");
        let terminal = terminal_session(&mut r);
        Fixture {
            identity: *bob.export(),
            store: store.to_bytes().to_vec(),
            session: session.export().to_vec(),
            terminal,
        }
    })
}

/// A responder session whose agreement has failed, made as `tacenta-core/tests/full_session.rs` makes one:
/// one bit of its stored Braid MAC key flipped, then messages delivered until the header completes.
fn terminal_session(r: &mut Stream) -> Vec<u8> {
    let alice = Identity::generate(r);
    let bob = Identity::generate(r);
    let mut store = bob.create_prekeys(2, r);
    let bundle = store.publish();
    let mut pending = establish_initiator(&alice, &bundle, &Expectation::first_contact(&[]), r)
        .expect("terminal fixture: establish the initiator");
    let first = pending
        .encrypt(b"terminal", r)
        .expect("terminal fixture: first message");
    let (session, _) = establish_responder(&bob, &mut store, &first, r)
        .expect("terminal fixture: establish the responder");
    let mut saved = session.export().to_vec();
    let triple_len = u32::from_be_bytes(saved[1..5].try_into().expect("four bytes")) as usize;
    let braid = 1 + 4 + triple_len + 4;
    saved[braid + 2 + 8 + 32] ^= 0x01;
    let mut session = Session::import(&saved).expect("terminal fixture: import");
    let mut i = 0u8;
    while !session.agreement_failed() {
        let m = pending.encrypt(&[i], r).expect("terminal fixture: send");
        session
            .decrypt(&m, r)
            .expect("terminal fixture: accepted until the refusals begin");
        i += 1;
        assert!(i < 8, "terminal fixture: the agreement did not fail");
    }
    session.export().to_vec()
}

const TOO_LONG: LifecycleError = LifecycleError::Decode(DecodeError::TooLong);

/// What one receiving operation did with a frame: its result, how many calls it made to the random source,
/// and whether the stored bytes it worked on are unchanged.
struct Outcome<T> {
    result: Result<T, LifecycleError>,
    calls: usize,
    unchanged: bool,
}

fn decrypt_on(stored: &[u8], frame: &[u8], seed: u64) -> Result<Outcome<Vec<u8>>, String> {
    let mut session = Session::import(stored).map_err(|e| format!("fixture session: {e:?}"))?;
    let mut rng = Stream::new(seed);
    let result = session.decrypt(frame, &mut rng);
    Ok(Outcome {
        result,
        calls: rng.calls,
        unchanged: session.export().as_slice() == stored,
    })
}

pub(crate) fn check(v: &Vector) -> Result<(), String> {
    let length = be32(&input(v, "length")?)? as usize;
    let prefix = input(v, "prefix")?;
    if prefix.len() > length {
        return Err("the prefix is longer than the frame".to_string());
    }
    let mut frame = vec![0u8; length];
    frame[..prefix.len()].copy_from_slice(&prefix);

    let fx = fixture();
    let live = decrypt_on(&fx.session, &frame, 1)?;
    let terminal = decrypt_on(&fx.terminal, &frame, 3)?;
    let mut store =
        PrekeyStore::from_bytes(&fx.store).map_err(|e| format!("fixture store: {e:?}"))?;
    let identity = Identity::from_secret(fx.identity);
    let mut rng = Stream::new(2);
    let established = Outcome {
        result: establish_responder(&identity, &mut store, &frame, &mut rng).map(|_| ()),
        calls: rng.calls,
        unchanged: store.to_bytes().as_slice() == fx.store.as_slice(),
    };

    if expects_success(v)? {
        if check_frame_size(&frame).is_err() {
            return Err("check_frame_size refuses a frame the vector admits".to_string());
        }
        let initial = message_type(&frame) == Some(MessageType::Initial);
        let initial_decode = decode_initial(&frame).err();
        let decoder_error = if initial {
            initial_decode
        } else {
            decode_message(&frame).err()
        };
        let span = ratchet_span(&frame).map(|n| (n as u32).to_be_bytes().to_vec());
        let decodes = vec![u8::from(decoder_error.is_none())];
        fields_eq(
            v,
            &[("ratchet_message_length", span), ("decodes", Some(decodes))],
        )?;
        for (name, outcome) in [
            ("the live session", &live),
            ("the terminal session", &terminal),
        ] {
            match &outcome.result {
                Ok(_) => return Err(format!("{name} accepted a frame of zeros")),
                Err(e) if *e == TOO_LONG => {
                    return Err(format!("{name} refused an admitted frame as too long"));
                }
                Err(_) => {}
            }
            if !outcome.unchanged {
                return Err(format!("{name}'s refusal changed it"));
            }
        }
        // On the session whose agreement has failed, the specified order (mlkem-braid.md, Failure): a frame
        // that is not an initial frame meets AgreementFailed before any decode; an initial frame meets its
        // decoder's refusal, or NotARepeatedInitial (none of these frames is that session's repeat). No draw.
        let terminal_want = match (&initial_decode, initial) {
            (_, false) => LifecycleError::AgreementFailed,
            (Some(e), true) => LifecycleError::Decode(*e),
            (None, true) => LifecycleError::NotARepeatedInitial,
        };
        if terminal.result.as_ref().err() != Some(&terminal_want) {
            return Err(format!(
                "the terminal session gave {:?}, not {terminal_want:?}",
                terminal.result.as_ref().err()
            ));
        }
        if terminal.calls != 0 {
            return Err(format!(
                "the terminal session's refusal read the random source ({} calls)",
                terminal.calls
            ));
        }
        // The refusal each frame had without the rule.
        let live_error = live.result.as_ref().err();
        match (&decoder_error, initial) {
            (Some(e), _) => {
                if live_error != Some(&LifecycleError::Decode(*e)) {
                    return Err(format!(
                        "the live session gave {live_error:?}, not its decoder's Decode({e:?})"
                    ));
                }
            }
            (None, true) => {
                if live_error != Some(&LifecycleError::NotARepeatedInitial) {
                    return Err(format!(
                        "the live session gave {live_error:?} for another handshake's initial frame"
                    ));
                }
            }
            (None, false) => {
                if matches!(live_error, Some(LifecycleError::Decode(_))) {
                    return Err(format!(
                        "the live session gave {live_error:?} for a frame that decodes"
                    ));
                }
            }
        }
        let want = match &initial_decode {
            Some(e) => LifecycleError::Decode(*e),
            None => LifecycleError::UnknownPrekeyId,
        };
        if established.result.as_ref().err() != Some(&want) {
            return Err(format!(
                "establish_responder gave {:?}, not {want:?}",
                established.result.err()
            ));
        }
        if !established.unchanged {
            return Err("establish_responder's refusal changed the store".to_string());
        }
        Ok(())
    } else {
        match v.refusal.as_deref() {
            Some("decode-failure") => {}
            other => {
                return Err(format!(
                    "a refused frame-size vector names decode-failure, not {other:?}"
                ));
            }
        }
        if check_frame_size(&frame) != Err(DecodeError::TooLong) {
            return Err("check_frame_size admits a frame the vector refuses".to_string());
        }
        for (name, result, calls, unchanged) in [
            (
                "Session::decrypt on the live session",
                live.result.as_ref().err(),
                live.calls,
                live.unchanged,
            ),
            (
                "Session::decrypt on the terminal session",
                terminal.result.as_ref().err(),
                terminal.calls,
                terminal.unchanged,
            ),
            (
                "establish_responder",
                established.result.as_ref().err(),
                established.calls,
                established.unchanged,
            ),
        ] {
            if result != Some(&TOO_LONG) {
                return Err(format!("{name} gave {result:?}, not Decode(TooLong)"));
            }
            if calls != 0 {
                return Err(format!(
                    "{name}: a size refusal read the random source ({calls} calls)"
                ));
            }
            if !unchanged {
                return Err(format!("{name}: a size refusal changed what it stored"));
            }
        }
        Ok(())
    }
}
