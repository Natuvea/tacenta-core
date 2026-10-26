//! The message size bound at the real constants (tacenta-spec/protocol/message-format.md, Message size).
//! **Tested only, on the inputs below; this is not a proof.**
//!
//! What each test drives is the public entry the specification names: `Session::encrypt` for the sender's
//! rule, `Session::decrypt` (on an established session, a ratchet frame and a repeated initial frame alike)
//! and `establish_responder` for the size rule. The frames are real ones from real sessions where the test
//! needs them to authenticate, and attacker-shaped ones (a lying `kem_ciphertext_len`, a malformed wrapper)
//! where it does not. The attacker here has the threat model's powers on the wire: any bytes, any length
//! prefix, the session's own identity and ephemeral copied out of a genuine frame.
//!
//! For every size refusal, the effects are checked as well as the error:
//!
//! * the random source is not read at all (a counting source records every call);
//! * the session's export is byte-equal before and after, and so is the prekey store's;
//! * the session still works afterwards: the genuine message behind the refused frame still decrypts.
//!
//! The exact limits are tested in both directions: a plaintext of `MAX_PLAINTEXT_LEN` bytes encrypts to a
//! frame of exactly `MAX_RATCHET_FRAME_LEN` (or `MAX_INITIAL_FRAME_LEN` while pending) and decrypts back, and
//! one byte more is refused. Peak memory is a few megabytes per call (zeroed buffers).
//!
//! `tooling/tests/run-message-size-cases.sh` runs this file, and the `MS-*` rows of
//! `tooling/gate-mutations.json` break each size check in turn (removed, off by one, moved after the decode or
//! after the draw, the nested check dropped) and require a named test here to fail.

use rand::SeedableRng;
use rand_core::{CryptoRng, RngCore};
use tacenta_core::serialization::{
    DecodeError, MAX_INITIAL_FRAME_LEN, MAX_PLAINTEXT_LEN, MAX_RATCHET_FRAME_LEN, check_frame_size,
    decode_initial, encode_initial, ratchet_span,
};
use tacenta_core::sessions::{
    self, Expectation, LifecycleError, PrekeyStore, Session, establish_initiator,
    establish_responder,
};

/// A seeded source that counts every call made to it.
struct Counting {
    inner: rand::rngs::StdRng,
    calls: usize,
}

impl Counting {
    fn new(seed: u64) -> Counting {
        Counting {
            inner: rand::rngs::StdRng::seed_from_u64(seed),
            calls: 0,
        }
    }
}

impl RngCore for Counting {
    fn next_u32(&mut self) -> u32 {
        self.calls += 1;
        self.inner.next_u32()
    }
    fn next_u64(&mut self) -> u64 {
        self.calls += 1;
        self.inner.next_u64()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.calls += 1;
        self.inner.fill_bytes(dest)
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.calls += 1;
        self.inner.try_fill_bytes(dest)
    }
}

impl CryptoRng for Counting {}

struct Parties {
    alice: Session,
    bob: Session,
    bob_id: sessions::Identity,
    bob_prekeys: PrekeyStore,
    /// The initial message that established Bob's session.
    initial: Vec<u8>,
}

/// Alice pending (her session still wraps every message), Bob established from her first message.
fn pending_pair(r: &mut Counting) -> Parties {
    let alice_id = sessions::Identity::generate(r);
    let bob_id = sessions::Identity::generate(r);
    let mut bob_prekeys = bob_id.create_prekeys(2, r);
    let bundle = bob_prekeys.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, &Expectation::first_contact(&[]), r)
        .expect("establish");
    let initial = alice.encrypt(b"first", r).expect("first message");
    let (bob, first) =
        establish_responder(&bob_id, &mut bob_prekeys, &initial, r).expect("responder");
    assert_eq!(first, b"first");
    Parties {
        alice,
        bob,
        bob_id,
        bob_prekeys,
        initial,
    }
}

/// Both established: Alice has read Bob's reply, so she sends bare ratchet messages.
fn established_pair(r: &mut Counting) -> Parties {
    let mut p = pending_pair(r);
    let reply = p.bob.encrypt(b"reply", r).expect("reply");
    assert_eq!(
        p.alice.decrypt(&reply, r).expect("reply decrypts"),
        b"reply"
    );
    p
}

/// Assert that `call` refuses with `expected`, reads the random source not at all, and leaves `session`
/// byte-for-byte as it was.
fn refused_without_effect(
    session: &mut Session,
    r: &mut Counting,
    expected: LifecycleError,
    call: impl FnOnce(&mut Session, &mut Counting) -> Result<Vec<u8>, LifecycleError>,
) {
    let before = session.export().to_vec();
    let calls = r.calls;
    let result = call(session, r);
    assert_eq!(result, Err(expected), "the refusal kind");
    assert_eq!(
        r.calls, calls,
        "a size refusal must not read the random source"
    );
    assert_eq!(
        session.export().to_vec(),
        before,
        "a size refusal must leave the session unchanged"
    );
}

/// The same for responder establishment: the store, not a session, is what must not change.
fn responder_refused_without_effect(
    p: &mut Parties,
    r: &mut Counting,
    frame: &[u8],
    expected: LifecycleError,
) {
    let before = p.bob_prekeys.to_bytes().to_vec();
    let calls = r.calls;
    let result = establish_responder(&p.bob_id, &mut p.bob_prekeys, frame, r);
    assert_eq!(result.err(), Some(expected), "the refusal kind");
    assert_eq!(
        r.calls, calls,
        "a size refusal must not read the random source"
    );
    assert_eq!(
        p.bob_prekeys.to_bytes().to_vec(),
        before,
        "a size refusal must leave the prekey store unchanged"
    );
}

const TOO_LONG: LifecycleError = LifecycleError::Decode(DecodeError::TooLong);

/// The fields of a decoded initial frame, re-wrapped around another ratchet message with another KEM
/// ciphertext. The wrapper is not authenticated, so this is what an attacker on the wire can do to a repeat.
fn rewrap(initial: &[u8], kem_ciphertext: &[u8], ratchet_message: &[u8]) -> Vec<u8> {
    let d = decode_initial(initial).expect("a genuine initial frame decodes");
    encode_initial(
        &d.identity,
        &d.ephemeral,
        kem_ciphertext,
        d.signed_prekey_id,
        d.one_time_prekey_id,
        d.kem_prekey_id,
        ratchet_message,
    )
}

fn inner_of(initial: &[u8]) -> Vec<u8> {
    decode_initial(initial).expect("decodes").message
}

#[test]
fn the_constants_are_the_specified_ones() {
    assert_eq!(MAX_PLAINTEXT_LEN, (1 << 20) - 1);
    assert_eq!(MAX_RATCHET_FRAME_LEN, 1_048_710);
    assert_eq!(MAX_INITIAL_FRAME_LEN, 1_050_362);
    assert_eq!(MAX_RATCHET_FRAME_LEN, 150 + 16 * (MAX_PLAINTEXT_LEN / 16));
    assert_eq!(MAX_INITIAL_FRAME_LEN, MAX_RATCHET_FRAME_LEN + 1_652);
}

#[test]
fn a_plaintext_at_the_maximum_round_trips_in_a_ratchet_frame_of_the_maximum() {
    let mut r = Counting::new(1);
    let mut p = established_pair(&mut r);
    let plaintext = vec![0u8; MAX_PLAINTEXT_LEN];
    let frame = p
        .alice
        .encrypt(&plaintext, &mut r)
        .expect("the maximum is accepted");
    assert_eq!(frame.len(), MAX_RATCHET_FRAME_LEN);
    assert_eq!(ratchet_span(&frame), Some(MAX_RATCHET_FRAME_LEN));
    let received = p
        .bob
        .decrypt(&frame, &mut r)
        .expect("the maximum frame decrypts");
    assert_eq!(received.len(), MAX_PLAINTEXT_LEN);
    assert!(received == plaintext);
}

#[test]
fn a_plaintext_one_over_is_refused_before_any_draw_on_an_established_session() {
    let mut r = Counting::new(2);
    let mut p = established_pair(&mut r);
    let plaintext = vec![0u8; MAX_PLAINTEXT_LEN + 1];
    refused_without_effect(
        &mut p.alice,
        &mut r,
        LifecycleError::PlaintextTooLong,
        |s, r| s.encrypt(&plaintext, r),
    );
    // Nothing was lost: the next message is the one the peer expects next.
    let next = p
        .alice
        .encrypt(b"after", &mut r)
        .expect("encrypt after the refusal");
    assert_eq!(p.bob.decrypt(&next, &mut r).expect("decrypt"), b"after");
}

#[test]
fn a_pending_initiator_sends_the_maximum_as_an_initial_frame_of_the_maximum() {
    let mut r = Counting::new(3);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);
    let bundle = bob_prekeys.publish();
    let mut alice =
        establish_initiator(&alice_id, &bundle, &Expectation::first_contact(&[]), &mut r).unwrap();
    let plaintext = vec![0u8; MAX_PLAINTEXT_LEN];
    // The first message, which establishes.
    let first = alice
        .encrypt(&plaintext, &mut r)
        .expect("the maximum is accepted");
    assert_eq!(first.len(), MAX_INITIAL_FRAME_LEN);
    assert_eq!(ratchet_span(&first), Some(MAX_RATCHET_FRAME_LEN));
    let (mut bob, received) =
        establish_responder(&bob_id, &mut bob_prekeys, &first, &mut r).expect("establishes");
    assert_eq!(received.len(), MAX_PLAINTEXT_LEN);
    // A repeat, still pending, of the maximum: the repeat path of `Session::decrypt`.
    let repeat = alice
        .encrypt(&plaintext, &mut r)
        .expect("a pending repeat at the maximum");
    assert_eq!(repeat.len(), MAX_INITIAL_FRAME_LEN);
    let received = bob
        .decrypt(&repeat, &mut r)
        .expect("the repeat at the maximum decrypts");
    assert_eq!(received.len(), MAX_PLAINTEXT_LEN);
}

#[test]
fn a_plaintext_one_over_is_refused_before_any_draw_on_a_pending_session() {
    let mut r = Counting::new(4);
    let mut p = pending_pair(&mut r);
    let plaintext = vec![0u8; MAX_PLAINTEXT_LEN + 1];
    refused_without_effect(
        &mut p.alice,
        &mut r,
        LifecycleError::PlaintextTooLong,
        |s, r| s.encrypt(&plaintext, r),
    );
    // Still pending: the next message is still an initial frame, and the responder reads it.
    let next = p.alice.encrypt(b"after", &mut r).expect("encrypt");
    assert_eq!(next[1], 0x02, "the session is still pending");
    assert_eq!(
        p.bob.decrypt(&next, &mut r).expect("repeat decrypts"),
        b"after"
    );
}

/// Before the session is pending at all, the first `encrypt` is what produces the initial message: refused
/// with the same kind, and the session still produces a first message afterwards.
#[test]
fn the_first_initial_message_is_held_to_the_sender_rule() {
    let mut r = Counting::new(5);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);
    let bundle = bob_prekeys.publish();
    let mut alice =
        establish_initiator(&alice_id, &bundle, &Expectation::first_contact(&[]), &mut r).unwrap();
    let plaintext = vec![0u8; MAX_PLAINTEXT_LEN + 1];
    refused_without_effect(
        &mut alice,
        &mut r,
        LifecycleError::PlaintextTooLong,
        |s, r| s.encrypt(&plaintext, r),
    );
    let first = alice.encrypt(b"short", &mut r).expect("first message");
    let (_bob, received) =
        establish_responder(&bob_id, &mut bob_prekeys, &first, &mut r).expect("establishes");
    assert_eq!(received, b"short");
}

#[test]
fn a_ratchet_frame_one_over_is_refused_before_any_draw() {
    let mut r = Counting::new(6);
    let mut p = established_pair(&mut r);
    let genuine = p.alice.encrypt(b"genuine", &mut r).expect("encrypt");
    // A frame of MAX_RATCHET_FRAME_LEN + 1 bytes beginning with the genuine frame: past the bound by one.
    let mut frame = genuine.clone();
    frame.resize(MAX_RATCHET_FRAME_LEN + 1, 0);
    assert_eq!(check_frame_size(&frame), Err(DecodeError::TooLong));
    refused_without_effect(&mut p.bob, &mut r, TOO_LONG, |s, r| s.decrypt(&frame, r));
    // At the bound exactly, the same frame is not refused for its size: it reaches the AEAD.
    frame.truncate(MAX_RATCHET_FRAME_LEN);
    assert_eq!(check_frame_size(&frame), Ok(()));
    assert_eq!(p.bob.decrypt(&frame, &mut r), Err(LifecycleError::Aead));
    // And the genuine message behind both still decrypts.
    assert_eq!(
        p.bob.decrypt(&genuine, &mut r).expect("decrypt"),
        b"genuine"
    );
}

#[test]
fn an_initial_frame_one_over_is_refused_by_the_session_and_the_responder() {
    let mut r = Counting::new(7);
    let mut p = pending_pair(&mut r);
    // A genuine repeat with an honest 1,568-byte KEM ciphertext, padded inside its ratchet message to one
    // byte over the initial bound.
    let repeat = p.alice.encrypt(b"repeat", &mut r).expect("encrypt");
    let mut frame = repeat.clone();
    frame.resize(MAX_INITIAL_FRAME_LEN + 1, 0);
    assert_eq!(check_frame_size(&frame), Err(DecodeError::TooLong));
    refused_without_effect(&mut p.bob, &mut r, TOO_LONG, |s, r| s.decrypt(&frame, r));
    responder_refused_without_effect(&mut p, &mut r, &frame, TOO_LONG);
    // The genuine repeat still decrypts.
    assert_eq!(p.bob.decrypt(&repeat, &mut r).expect("decrypt"), b"repeat");
}

/// **The nested-wrapper bypass.** `Session::decrypt` never reads an initial frame's KEM ciphertext, and the
/// decoder accepts any `kem_ciphertext_len`, so a repeat re-wrapped with an empty KEM ciphertext has room for
/// a ratchet message 1,568 bytes longer than the ratchet bound inside a frame within the initial bound. The
/// size rule locates the ratchet message through the frame's own length field and refuses it.
#[test]
fn a_rewrapped_repeat_with_an_empty_kem_ciphertext_cannot_carry_an_oversized_ratchet_message() {
    let mut r = Counting::new(8);
    let mut p = pending_pair(&mut r);
    let repeat = p
        .alice
        .encrypt(&vec![0u8; MAX_PLAINTEXT_LEN], &mut r)
        .expect("encrypt");
    let inner = inner_of(&repeat);
    assert_eq!(inner.len(), MAX_RATCHET_FRAME_LEN);

    // One byte over the ratchet bound inside, the whole frame well under the initial bound.
    let mut long_inner = inner.clone();
    long_inner.push(0);
    let frame = rewrap(&repeat, &[], &long_inner);
    assert_eq!(frame.len(), MAX_RATCHET_FRAME_LEN + 85);
    assert!(frame.len() <= MAX_INITIAL_FRAME_LEN);
    assert_eq!(check_frame_size(&frame), Err(DecodeError::TooLong));
    refused_without_effect(&mut p.bob, &mut r, TOO_LONG, |s, r| s.decrypt(&frame, r));
    responder_refused_without_effect(&mut p, &mut r, &frame, TOO_LONG);

    // The measured case: a frame of exactly MAX_INITIAL_FRAME_LEN bytes whose ratchet message is 1,050,278.
    let mut longest = inner.clone();
    longest.resize(MAX_INITIAL_FRAME_LEN - 84, 0);
    let frame = rewrap(&repeat, &[], &longest);
    assert_eq!(frame.len(), MAX_INITIAL_FRAME_LEN);
    assert_eq!(ratchet_span(&frame), Some(1_050_278));
    refused_without_effect(&mut p.bob, &mut r, TOO_LONG, |s, r| s.decrypt(&frame, r));
    responder_refused_without_effect(&mut p, &mut r, &frame, TOO_LONG);

    // A KEM ciphertext one byte short of the honest one, the frame at the initial bound: one over inside.
    let mut short_kem_inner = inner.clone();
    short_kem_inner.push(0);
    let frame = rewrap(&repeat, &[0u8; 1567], &short_kem_inner);
    assert_eq!(frame.len(), MAX_INITIAL_FRAME_LEN);
    refused_without_effect(&mut p.bob, &mut r, TOO_LONG, |s, r| s.decrypt(&frame, r));

    // At the ratchet bound inside, the re-wrapped repeat is accepted: the rule refuses length, not the
    // re-wrap (session-establishment.md: the wrapper's other fields are not compared).
    let frame = rewrap(&repeat, &[], &inner);
    assert_eq!(check_frame_size(&frame), Ok(()));
    let received = p
        .bob
        .decrypt(&frame, &mut r)
        .expect("a re-wrap within the bounds decrypts");
    assert_eq!(received.len(), MAX_PLAINTEXT_LEN);
}

/// The size rule wins over every other refusal: an input that is too long and also malformed, or not a
/// repeat, or that names a prekey the store does not hold, is refused as too long.
#[test]
fn an_oversized_input_is_refused_as_too_long_whatever_else_is_wrong_with_it() {
    let mut r = Counting::new(9);
    let mut p = pending_pair(&mut r);

    // An unknown version byte, one over the ratchet bound (it is not an initial frame).
    let mut bad_version = vec![0u8; MAX_RATCHET_FRAME_LEN + 1];
    bad_version[1] = 0x02;
    refused_without_effect(&mut p.bob, &mut r, TOO_LONG, |s, r| {
        s.decrypt(&bad_version, r)
    });
    responder_refused_without_effect(&mut p, &mut r, &bad_version, TOO_LONG);

    // An initial frame whose keys lack their curve byte (the decoder's WrongType), with an empty KEM
    // ciphertext and a ratchet message one over.
    let mut no_curve = vec![0u8; 84 + MAX_RATCHET_FRAME_LEN + 1];
    no_curve[0] = 0x01;
    no_curve[1] = 0x02;
    assert_eq!(
        decode_initial(&no_curve[..200]).err(),
        Some(DecodeError::WrongType)
    );
    refused_without_effect(&mut p.bob, &mut r, TOO_LONG, |s, r| s.decrypt(&no_curve, r));
    responder_refused_without_effect(&mut p, &mut r, &no_curve, TOO_LONG);

    // A KEM length that runs past the end (the decoder's LengthOverrun), one over the initial bound.
    let mut overrun = p.initial.clone();
    overrun[68..72].copy_from_slice(&u32::MAX.to_be_bytes());
    overrun.resize(MAX_INITIAL_FRAME_LEN + 1, 0);
    refused_without_effect(&mut p.bob, &mut r, TOO_LONG, |s, r| s.decrypt(&overrun, r));
    responder_refused_without_effect(&mut p, &mut r, &overrun, TOO_LONG);

    // An initial frame from another handshake (NotARepeatedInitial on Bob's session), oversized inside.
    let other_id = sessions::Identity::generate(&mut r);
    let bundle = p.bob_prekeys.publish();
    let mut other =
        establish_initiator(&other_id, &bundle, &Expectation::first_contact(&[]), &mut r).unwrap();
    let other_first = other.encrypt(b"other", &mut r).unwrap();
    let mut other_inner = inner_of(&other_first);
    other_inner.resize(MAX_RATCHET_FRAME_LEN + 1, 0);
    let frame = rewrap(&other_first, &[], &other_inner);
    refused_without_effect(&mut p.bob, &mut r, TOO_LONG, |s, r| s.decrypt(&frame, r));
    // And on the initiator's own session, which refuses every initial frame as not a repeat.
    refused_without_effect(&mut p.alice, &mut r, TOO_LONG, |s, r| s.decrypt(&frame, r));

    // A prekey identifier the store does not hold (UnknownPrekeyId), oversized inside.
    let d = decode_initial(&other_first).unwrap();
    let unknown = encode_initial(
        &d.identity,
        &d.ephemeral,
        &[],
        0xdead_beef,
        d.one_time_prekey_id,
        d.kem_prekey_id,
        &other_inner,
    );
    responder_refused_without_effect(&mut p, &mut r, &unknown, TOO_LONG);
}

/// Below the bounds every refusal is the one it was: the size rule changes nothing for a frame it admits.
#[test]
fn a_frame_the_rule_admits_keeps_its_existing_refusal() {
    let mut r = Counting::new(10);
    let mut p = pending_pair(&mut r);
    // An initial frame too short to hold its KEM length: TooShort, from the decoder.
    let short = p.initial[..71].to_vec();
    assert_eq!(check_frame_size(&short), Ok(()));
    assert_eq!(ratchet_span(&short), None);
    assert_eq!(
        p.bob.decrypt(&short, &mut r),
        Err(LifecycleError::Decode(DecodeError::TooShort))
    );
    // A KEM length that runs past the end, at the initial bound exactly: LengthOverrun.
    let mut overrun = p.initial.clone();
    overrun[68..72].copy_from_slice(&u32::MAX.to_be_bytes());
    overrun.resize(MAX_INITIAL_FRAME_LEN, 0);
    assert_eq!(check_frame_size(&overrun), Ok(()));
    assert_eq!(
        p.bob.decrypt(&overrun, &mut r),
        Err(LifecycleError::Decode(DecodeError::LengthOverrun))
    );
    let before = p.bob_prekeys.to_bytes().to_vec();
    assert_eq!(
        establish_responder(&p.bob_id, &mut p.bob_prekeys, &overrun, &mut r).err(),
        Some(LifecycleError::Decode(DecodeError::LengthOverrun))
    );
    assert_eq!(p.bob_prekeys.to_bytes().to_vec(), before);
    // A ratchet frame at the bound with an unknown version byte: UnknownVersion, from the decoder.
    let mut unknown = vec![0u8; MAX_RATCHET_FRAME_LEN];
    unknown[1] = 0x01;
    assert_eq!(
        p.bob.decrypt(&unknown, &mut r),
        Err(LifecycleError::Decode(DecodeError::UnknownVersion))
    );
    // An empty frame: TooShort.
    assert_eq!(
        p.bob.decrypt(&[], &mut r),
        Err(LifecycleError::Decode(DecodeError::TooShort))
    );
}

/// A session whose agreement has failed refuses as too long first, on both sides.
#[test]
fn a_terminal_session_refuses_oversized_inputs_as_too_long() {
    let mut r = Counting::new(11);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);
    let bundle = bob_prekeys.publish();
    let mut alice =
        establish_initiator(&alice_id, &bundle, &Expectation::first_contact(&[]), &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();
    let (bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    // Fail Bob's Braid as tests/full_session.rs does: flip one bit of its saved MAC key, then deliver until
    // the header completes on his side.
    let mut saved = bob.export().to_vec();
    let triple_len = u32::from_be_bytes(saved[1..5].try_into().unwrap()) as usize;
    let braid = 1 + 4 + triple_len + 4;
    saved[braid + 2 + 8 + 32] ^= 0x01;
    let mut bob = Session::import(&saved).expect("import");
    let mut i = 0u8;
    while !bob.agreement_failed() {
        let m = alice.encrypt(&[i], &mut r).unwrap();
        bob.decrypt(&m, &mut r)
            .expect("accepted until the refusals begin");
        i += 1;
        assert!(i < 8, "the agreement did not fail");
    }
    // The terminal refusal, below the bounds.
    assert_eq!(
        bob.encrypt(b"x", &mut r),
        Err(LifecycleError::AgreementFailed)
    );
    // Above them, too long first, with no effect.
    let plaintext = vec![0u8; MAX_PLAINTEXT_LEN + 1];
    refused_without_effect(
        &mut bob,
        &mut r,
        LifecycleError::PlaintextTooLong,
        |s, r| s.encrypt(&plaintext, r),
    );
    // Alice is still pending, so her frame is an initial frame: one over the initial bound, and, re-wrapped
    // with an empty KEM ciphertext, one over the ratchet bound inside.
    let genuine = alice.encrypt(b"y", &mut r).unwrap();
    let mut frame = genuine.clone();
    frame.resize(MAX_INITIAL_FRAME_LEN + 1, 0);
    refused_without_effect(&mut bob, &mut r, TOO_LONG, |s, r| s.decrypt(&frame, r));
    let mut inner = inner_of(&genuine);
    inner.resize(MAX_RATCHET_FRAME_LEN + 1, 0);
    let nested = rewrap(&genuine, &[], &inner);
    refused_without_effect(&mut bob, &mut r, TOO_LONG, |s, r| s.decrypt(&nested, r));
    // Within the bounds, the terminal refusal is what it was.
    assert_eq!(
        bob.decrypt(&genuine, &mut r),
        Err(LifecycleError::AgreementFailed)
    );
}
