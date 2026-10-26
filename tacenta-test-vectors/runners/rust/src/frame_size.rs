//! The size rule's vectors (`vectors/serialization/frame-size.json`; tacenta-spec/protocol/message-format.md,
//! Message size), checked against the two receiving operations that apply it.
//!
//! A vector gives a frame's `length`, four bytes big-endian, and its `prefix`; the frame is the prefix
//! followed by zero bytes up to the length (tacenta-test-vectors/README.md, Vector layouts). The runner builds
//! it and hands it to `Session::decrypt`, on a responder session, and to `establish_responder`, on a prekey
//! store, both rebuilt from the same stored bytes for every vector.
//!
//! * An invalid vector is refused by both as `Decode(DecodeError::TooLong)`, with the session's and the
//!   store's stored bytes unchanged and the random source not read; `check_frame_size` refuses it too.
//! * A valid vector is admitted by `check_frame_size`, and neither operation refuses it as too long (each
//!   refuses it later, for other reasons, since the frames are mostly zeros). `ratchet_span` gives the length
//!   the vector names in `fields`, and gives none when the vector leaves the field out.

use std::sync::OnceLock;

use rand_core::{CryptoRng, RngCore};
use tacenta_core::serialization::{DecodeError, check_frame_size, ratchet_span};
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
}

/// A responder session established from a real initial message, and the store it left.
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
        Fixture {
            identity: *bob.export(),
            store: store.to_bytes().to_vec(),
            session: session.export().to_vec(),
        }
    })
}

const TOO_LONG: LifecycleError = LifecycleError::Decode(DecodeError::TooLong);

pub(crate) fn check(v: &Vector) -> Result<(), String> {
    let length = be32(&input(v, "length")?)? as usize;
    let prefix = input(v, "prefix")?;
    if prefix.len() > length {
        return Err("the prefix is longer than the frame".to_string());
    }
    let mut frame = vec![0u8; length];
    frame[..prefix.len()].copy_from_slice(&prefix);

    let fx = fixture();
    let mut session =
        Session::import(&fx.session).map_err(|e| format!("fixture session: {e:?}"))?;
    let mut store =
        PrekeyStore::from_bytes(&fx.store).map_err(|e| format!("fixture store: {e:?}"))?;
    let identity = Identity::from_secret(fx.identity);

    let mut rng = Stream::new(1);
    let decrypted = session.decrypt(&frame, &mut rng);
    let decrypt_calls = rng.calls;
    let session_unchanged = session.export().as_slice() == fx.session.as_slice();
    let mut rng = Stream::new(2);
    let established = establish_responder(&identity, &mut store, &frame, &mut rng).err();
    let establish_calls = rng.calls;
    let store_unchanged = store.to_bytes().as_slice() == fx.store.as_slice();

    if expects_success(v)? {
        if check_frame_size(&frame).is_err() {
            return Err("check_frame_size refuses a frame the vector admits".to_string());
        }
        let span = ratchet_span(&frame).map(|n| (n as u32).to_be_bytes().to_vec());
        fields_eq(v, &[("ratchet_message_length", span)])?;
        if decrypted.as_ref().err() == Some(&TOO_LONG) {
            return Err("Session::decrypt refused an admitted frame as too long".to_string());
        }
        if established == Some(TOO_LONG) {
            return Err("establish_responder refused an admitted frame as too long".to_string());
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
        match decrypted {
            Err(e) if e == TOO_LONG => {}
            other => {
                return Err(format!(
                    "Session::decrypt gave {other:?}, not Decode(TooLong)"
                ));
            }
        }
        if established != Some(TOO_LONG) {
            return Err(format!(
                "establish_responder gave {established:?}, not Decode(TooLong)"
            ));
        }
        if decrypt_calls != 0 || establish_calls != 0 {
            return Err(format!(
                "a size refusal read the random source ({decrypt_calls} and {establish_calls} calls)"
            ));
        }
        if !session_unchanged || !store_unchanged {
            return Err("a size refusal changed the session or the store".to_string());
        }
        Ok(())
    }
}
