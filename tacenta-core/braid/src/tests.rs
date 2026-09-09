//! What these check.
//!
//! Reaching agreement at all is the first thing, because a state machine can
//! satisfy every property stated about it and still deadlock in round three.
//! `Model.Braid` runs the same exchange against a toy KEM and this runs it
//! against real ML-KEM, so the two agree on the shape and this one also says
//! the cryptography lines up.
//!
//! The rest are the failure paths, which are the ones that matter: a session
//! that reaches agreement when it should not is worth more to an attacker than
//! one that stalls.

use super::*;
use rand::SeedableRng;
use rand::rngs::StdRng;

fn rng(seed: u64) -> StdRng {
    StdRng::seed_from_u64(seed)
}

/// One party speaks and the other hears, then the other way round. Strict
/// alternation, which is the hardest schedule for a protocol built to send in
/// parallel.
struct Pair {
    a: Braid,
    b: Braid,
    a_out: Vec<Output>,
    b_out: Vec<Output>,
    a_reported: u64,
    b_reported: u64,
}

impl Pair {
    fn new(secret: &[u8]) -> Pair {
        Pair {
            a: Braid::initiator(secret),
            b: Braid::responder(secret),
            a_out: Vec::new(),
            b_out: Vec::new(),
            a_reported: 0,
            b_reported: 0,
        }
    }

    /// Receive and adopt in one step.
    ///
    /// Real callers must not do this. `receive` hands back a candidate so the
    /// authenticator of the message carrying it can be checked between deriving
    /// and adopting, and these tests have no such message: they exercise the
    /// agreement's own state machine. The transaction itself is covered by
    /// `an_uncommitted_receive_changes_nothing` below.
    fn receive_and_commit(b: &mut Braid, m: &Msg) -> (u64, Option<Output>) {
        let (rep, out, next) = b.receive(m);
        b.commit(next);
        (rep, out)
    }

    fn round<R: RngCore + CryptoRng>(&mut self, rng: &mut R) {
        let (m, rep, out, next) = self.a.send(rng);
        self.a = next;
        self.a_reported = rep;
        if let Some(o) = out {
            self.a_out.push(o);
        }
        let (rep, out) = Pair::receive_and_commit(&mut self.b, &m);
        self.b_reported = rep;
        if let Some(o) = out {
            self.b_out.push(o);
        }

        let (m, rep, out, next) = self.b.send(rng);
        self.b = next;
        self.b_reported = rep;
        if let Some(o) = out {
            self.b_out.push(o);
        }
        let (rep, out) = Pair::receive_and_commit(&mut self.a, &m);
        self.a_reported = rep;
        if let Some(o) = out {
            self.a_out.push(o);
        }
    }

    fn run<R: RngCore + CryptoRng>(&mut self, rounds: usize, rng: &mut R) {
        let mut i = 0;
        while i < rounds {
            self.round(rng);
            i += 1;
        }
    }
}

#[test]
fn both_parties_reach_the_same_key_for_the_first_epoch() {
    let mut r = rng(1);
    let mut p = Pair::new(b"a preshared secret from the handshake");
    p.run(200, &mut r);

    assert!(!p.a.failed(), "initiator failed: {}", p.a.state_name());
    assert!(!p.b.failed(), "responder failed: {}", p.b.state_name());
    assert!(!p.a_out.is_empty(), "initiator produced no key");
    assert!(!p.b_out.is_empty(), "responder produced no key");
    assert_eq!(p.a_out[0].key_epoch, 1);
    assert_eq!(p.b_out[0].key_epoch, 1);
    assert_eq!(p.a_out[0].key, p.b_out[0].key);
}

#[test]
fn the_agreement_keeps_going_and_the_roles_swap() {
    let mut r = rng(2);
    let mut p = Pair::new(b"secret");
    p.run(900, &mut r);

    assert!(!p.a.failed() && !p.b.failed());
    // Several epochs, and every one agreed on by both sides with the same
    // label. Epoch n is the responder's to sample when n is odd and the
    // initiator's when it is even, so this also says the swap happens.
    let n = p.a_out.len().min(p.b_out.len());
    assert!(n >= 3, "only {n} epochs completed");
    let mut i = 0;
    while i < n {
        assert_eq!(p.a_out[i].key_epoch, (i + 1) as u64);
        assert_eq!(p.b_out[i].key_epoch, (i + 1) as u64);
        assert_eq!(p.a_out[i].key, p.b_out[i].key, "epoch {}", i + 1);
        i += 1;
    }
}

#[test]
fn every_key_is_different_from_the_last() {
    let mut r = rng(3);
    let mut p = Pair::new(b"secret");
    p.run(900, &mut r);
    let mut i = 1;
    while i < p.a_out.len() {
        assert_ne!(p.a_out[i].key, p.a_out[i - 1].key);
        i += 1;
    }
}

#[test]
fn fresh_randomness_gives_a_different_key() {
    let mut p = Pair::new(b"secret");
    let mut q = Pair::new(b"secret");
    p.run(200, &mut rng(4));
    q.run(200, &mut rng(5));
    assert!(!p.a_out.is_empty() && !q.a_out.is_empty());
    assert_ne!(p.a_out[0].key, q.a_out[0].key);
}

#[test]
fn the_epoch_key_does_not_depend_on_the_preshared_secret() {
    // A characterisation test, pinning something surprising rather than
    // something desirable.
    //
    // KDF_OK takes the KEM shared secret and the epoch, with a zero salt. The
    // preshared secret from the handshake never enters it: it seeds the
    // Ratcheted Authenticator and nothing else. So two sessions that agree on
    // nothing except their randomness produce the same epoch key.
    //
    // That is the protocol as specified, and it is why a
    // Braid output must never be used as a session key on its own. Binding to
    // the session comes from the composition above, where the Triple Ratchet
    // mixes this into a root key that does depend on the handshake. This test
    // exists so that if the derivation ever changes, deliberately or otherwise,
    // it is a visible event rather than a silent one.
    let mut p = Pair::new(b"one secret");
    let mut q = Pair::new(b"an entirely different secret");
    p.run(200, &mut rng(4));
    q.run(200, &mut rng(4));
    assert!(!p.a_out.is_empty() && !q.a_out.is_empty());
    assert_eq!(p.a_out[0].key, q.a_out[0].key);
    assert_eq!(p.b_out[0].key, q.b_out[0].key);
}

#[test]
fn the_reported_epoch_never_runs_ahead_of_the_agreement() {
    let mut r = rng(5);
    let mut p = Pair::new(b"secret");
    let mut i = 0;
    while i < 400 {
        p.round(&mut r);
        // A party never claims agreement on an epoch for which it has not
        // produced a key. This is the property the whole sending_epoch and
        // receiving_epoch apparatus exists for, and the one Model.Braid proves
        // the accounting of.
        assert!(p.a_reported <= p.a_out.len() as u64);
        assert!(p.b_reported <= p.b_out.len() as u64);
        i += 1;
    }
}

#[test]
fn a_forged_header_mac_abandons_the_session() {
    let mut r = rng(6);
    let mut a = Braid::initiator(b"secret");
    // The responder holds a different secret, so its authenticator derives a
    // different MAC key and the header it receives will not verify.
    let mut b = Braid::responder(b"a different secret");
    let mut i = 0;
    while i < 20 && !b.failed() {
        let (m, _, _, next) = a.send(&mut r);
        a = next;
        Pair::receive_and_commit(&mut b, &m);
        i += 1;
    }
    assert!(
        b.failed(),
        "responder accepted a header it could not authenticate"
    );
}

#[test]
fn a_tampered_header_chunk_abandons_the_session() {
    let mut r = rng(7);
    let mut a = Braid::initiator(b"secret");
    let mut b = Braid::responder(b"secret");
    let mut i = 0;
    while i < 20 && !b.failed() {
        let (mut m, _, _, next) = a.send(&mut r);
        a = next;
        if let Some(c) = m.data.as_mut() {
            c.data[0] ^= 1;
        }
        Pair::receive_and_commit(&mut b, &m);
        i += 1;
    }
    assert!(b.failed(), "responder accepted a corrupted header");
}

#[test]
fn nothing_leaves_the_failed_state() {
    let mut r = rng(8);
    let mut a = Braid::initiator(b"secret");
    let mut b = Braid::responder(b"other");
    let mut i = 0;
    while i < 20 && !b.failed() {
        let (m, _, _, next) = a.send(&mut r);
        a = next;
        Pair::receive_and_commit(&mut b, &m);
        i += 1;
    }
    assert!(b.failed());
    // Drive it hard afterwards. It must stay failed and must never emit a key.
    let mut i = 0;
    while i < 100 {
        let (m, _, out, next) = b.send(&mut r);
        b = next;
        assert!(out.is_none());
        assert!(b.failed());
        let (_, out) = Pair::receive_and_commit(&mut b, &m);
        assert!(out.is_none());
        assert!(b.failed());
        i += 1;
    }
}

#[test]
fn messages_from_the_wrong_epoch_are_ignored_rather_than_fatal() {
    let mut r = rng(9);
    let mut p = Pair::new(b"secret");
    // Feed the responder well-formed messages stamped with an epoch it is not
    // negotiating. It should neither advance nor fail: it should simply not
    // care. This is the liveness cost recorded on the specification page.
    let mut i = 0;
    while i < 50 {
        let (mut m, _, _, next) = p.a.send(&mut r);
        p.a = next;
        m.epoch = 9999;
        let (_, out) = Pair::receive_and_commit(&mut p.b, &m);
        assert!(out.is_none());
        assert!(!p.b.failed());
        assert_eq!(p.b.epoch(), 1);
        i += 1;
    }
}

#[test]
fn a_replayed_chunk_does_not_advance_the_far_side() {
    let mut r = rng(10);
    let a = Braid::initiator(b"secret");
    let mut b = Braid::responder(b"secret");
    // The sender's next state is deliberately dropped: this test is about what
    // the *receiver* does with one codeword delivered repeatedly, and the
    // candidate-shaped send makes discarding it explicit rather than implicit.
    let (m, _, _, _) = a.send(&mut r);
    let before = b.state_name();
    let mut i = 0;
    while i < 100 {
        Pair::receive_and_commit(&mut b, &m);
        i += 1;
    }
    // One codeword replayed a hundred times is still one codeword.
    assert_eq!(b.state_name(), before);
    assert!(!b.failed());
}

#[test]
fn loss_delays_agreement_without_preventing_it() {
    let mut r = rng(11);
    let mut p = Pair::new(b"secret");
    // Drop two messages in three, in both directions.
    let mut i = 0usize;
    while i < 1200 {
        let (m, _, out, next) = p.a.send(&mut r);
        p.a = next;
        if let Some(o) = out {
            p.a_out.push(o);
        }
        if i.is_multiple_of(3) {
            let (_, out) = Pair::receive_and_commit(&mut p.b, &m);
            if let Some(o) = out {
                p.b_out.push(o);
            }
        }
        let (m, _, out, next) = p.b.send(&mut r);
        p.b = next;
        if let Some(o) = out {
            p.b_out.push(o);
        }
        if i.is_multiple_of(3) {
            let (_, out) = Pair::receive_and_commit(&mut p.a, &m);
            if let Some(o) = out {
                p.a_out.push(o);
            }
        }
        i += 1;
    }
    assert!(!p.a.failed() && !p.b.failed());
    assert!(!p.a_out.is_empty() && !p.b_out.is_empty());
    assert_eq!(p.a_out[0].key, p.b_out[0].key);
}

/// An uncommitted receive changes nothing.
///
/// `receive` takes `&self` and returns the next state as a candidate, so a
/// received message, which drives three state machines, can be rolled back on
/// this one as on the two ratchets beside it: a message that never
/// authenticates does not move the agreement forward.
#[test]
fn an_uncommitted_receive_changes_nothing() {
    let mut r = rng(77);
    let mut p = Pair::new(b"a preshared secret from the handshake");

    // Far enough in to have something to lose. An epoch takes a few hundred
    // messages, because the agreement streams its key material through the
    // erasure code a chunk at a time.
    p.run(200, &mut r);
    assert!(!p.a_out.is_empty(), "the warm-up completed no epoch");
    let completed = p.b_out.len();

    // Feed `b` a run of genuine, *different* messages without committing any of
    // them, and watch its own account of itself.
    //
    // Repeating one message would prove nothing: a chunk the decoder already
    // holds is idempotent, so an in-place receive answers the same way twice
    // and an in-place advance would go unnoticed. What moves this state
    // machine is a message that causes a transition, and only a sequence
    // contains one, so a test that repeated a single message would pass
    // against the very implementation it is written to reject.
    let name_before = p.b.state_name();
    let reported_before = p.b.reported();
    let mut held = Vec::new();
    for _ in 0..40 {
        let (m, _, _, next) = p.a.send(&mut r);
        p.a = next;
        let (rep, out, _candidate) = p.b.receive(&m);
        assert_eq!(
            p.b.state_name(),
            name_before,
            "an uncommitted receive moved the state machine"
        );
        assert_eq!(
            p.b.reported(),
            reported_before,
            "an uncommitted receive moved the reported epoch"
        );
        assert_eq!(rep, reported_before);
        assert!(out.is_none() || completed == p.b_out.len());
        held.push(m);
    }
    assert_eq!(
        p.b_out.len(),
        completed,
        "an uncommitted receive produced a key the caller never accepted"
    );

    // Now commit them in order. The agreement should be exactly where it would
    // have been had the uncommitted passes never happened.
    for m in &held {
        Pair::receive_and_commit(&mut p.b, m);
    }

    // And the agreement keeps reaching agreement afterwards.
    p.run(400, &mut r);
    assert!(!p.a.failed(), "initiator failed: {}", p.a.state_name());
    assert!(!p.b.failed(), "responder failed: {}", p.b.state_name());
    assert!(
        p.b_out.len() > completed,
        "no further epoch completed after an uncommitted receive"
    );
    let n = p.a_out.len().min(p.b_out.len());
    for i in 0..n {
        assert_eq!(
            p.a_out[i].key, p.b_out[i].key,
            "the two sides disagree on epoch {}",
            p.a_out[i].key_epoch
        );
    }
}

/// Every step of a real negotiation, round-tripped through `to_bytes`/
/// `from_bytes` and continued from the restored copy on both sides. This
/// exercises whichever of the eleven live states each step actually reaches,
/// rather than hand-selecting one, and the negotiation still has to complete
/// with agreeing keys afterward.
#[test]
fn to_bytes_from_bytes_round_trips_through_a_full_negotiation() {
    let mut r = rng(20);
    let mut p = Pair::new(b"a preshared secret from the handshake");
    let mut i = 0;
    while i < 300 {
        p.round(&mut r);

        let bytes_a = p.a.to_bytes();
        let restored_a = Braid::from_bytes(&bytes_a).unwrap();
        assert_eq!(restored_a.state_tag(), p.a.state_tag());
        assert_eq!(restored_a.epoch(), p.a.epoch());
        p.a = restored_a;

        let bytes_b = p.b.to_bytes();
        let restored_b = Braid::from_bytes(&bytes_b).unwrap();
        assert_eq!(restored_b.state_tag(), p.b.state_tag());
        assert_eq!(restored_b.epoch(), p.b.epoch());
        p.b = restored_b;

        i += 1;
    }
    assert!(!p.a.failed() && !p.b.failed());
    assert!(!p.a_out.is_empty() && !p.b_out.is_empty());
    let n = p.a_out.len().min(p.b_out.len());
    assert!(n >= 2, "only {n} epochs completed");
    let mut j = 0;
    while j < n {
        assert_eq!(p.a_out[j].key, p.b_out[j].key, "epoch {}", j + 1);
        j += 1;
    }
}

/// The `Failed` state -- the simplest one, and the one every other test in
/// this file relies on staying terminal -- round-trips too.
#[test]
fn to_bytes_from_bytes_round_trips_the_failed_state() {
    let mut r = rng(21);
    let mut a = Braid::initiator(b"secret");
    let mut b = Braid::responder(b"a different secret");
    let mut i = 0;
    while i < 20 && !b.failed() {
        let (m, _, _, next) = a.send(&mut r);
        a = next;
        Pair::receive_and_commit(&mut b, &m);
        i += 1;
    }
    assert!(b.failed());
    let bytes = b.to_bytes();
    let restored = Braid::from_bytes(&bytes).unwrap();
    assert!(restored.failed());
}

#[test]
fn from_bytes_rejects_a_foreign_version() {
    let a = Braid::initiator(b"secret");
    let mut bytes = a.to_bytes();
    bytes[0] = 0xff;
    assert!(matches!(
        Braid::from_bytes(&bytes),
        Err(BraidDecodeError::UnknownVersion)
    ));
}

#[test]
fn from_bytes_rejects_a_truncated_buffer() {
    let a = Braid::initiator(b"secret");
    let bytes = a.to_bytes();
    assert!(matches!(
        Braid::from_bytes(&bytes[..bytes.len() - 1]),
        Err(BraidDecodeError::Malformed)
    ));
}

#[test]
fn from_bytes_rejects_an_unknown_tag() {
    let a = Braid::initiator(b"secret");
    let mut bytes = a.to_bytes();
    bytes[1] = 200;
    assert!(matches!(
        Braid::from_bytes(&bytes),
        Err(BraidDecodeError::Malformed)
    ));
}

#[test]
fn from_bytes_rejects_trailing_bytes() {
    let a = Braid::initiator(b"secret");
    let mut bytes = a.to_bytes();
    bytes.push(0x00);
    assert!(matches!(
        Braid::from_bytes(&bytes),
        Err(BraidDecodeError::Malformed)
    ));
}

/// A persisted epoch of `u64::MAX` is refused as malformed rather than
/// restored (CR-03). No honest run reaches that epoch, and restoring it would
/// hand back a Braid whose next transition abandons the session; refusing it
/// is also what makes the T1 precondition `epoch < u64::MAX` true of every
/// state this crate constructs.
#[test]
fn from_bytes_refuses_an_epoch_at_the_ceiling() {
    let a = Braid::initiator(b"secret");
    let mut bytes = a.to_bytes();
    // Version, tag, then the eight epoch bytes.
    bytes[2..10].copy_from_slice(&u64::MAX.to_be_bytes());
    assert!(matches!(
        Braid::from_bytes(&bytes),
        Err(BraidDecodeError::Malformed)
    ));
    // One below the ceiling is an epoch like any other.
    bytes[2..10].copy_from_slice(&(u64::MAX - 1).to_be_bytes());
    assert!(Braid::from_bytes(&bytes).is_ok());
}

/// A persisted epoch of zero is refused as malformed. Both constructors
/// start at one and nothing counts down, so no run produced it; and the
/// epoch a caller reads is the negotiated one less one, so a restored
/// epoch-zero Braid would report an epoch of zero as "known to both
/// parties" and label the first completed epoch wrongly. Checked for
/// every state that carries an epoch: `Failed` carries none.
#[test]
fn from_bytes_refuses_epoch_zero() {
    let mut r = rng(32);
    let mut p = Pair::new(b"a preshared secret from the handshake");
    let mut samples: Vec<Option<Zeroizing<Vec<u8>>>> = vec![None; 11];
    let mut i = 0usize;
    while i < 1500 {
        let (m, _, _, next) = p.a.send(&mut r);
        p.a = next;
        Pair::receive_and_commit(&mut p.b, &m);
        let (m, _, _, next) = p.b.send(&mut r);
        p.b = next;
        if i.is_multiple_of(3) {
            Pair::receive_and_commit(&mut p.a, &m);
        }
        let ta = p.a.state_tag() as usize;
        if ta < 11 && samples[ta].is_none() {
            samples[ta] = Some(p.a.to_bytes());
        }
        let tb = p.b.state_tag() as usize;
        if tb < 11 && samples[tb].is_none() {
            samples[tb] = Some(p.b.to_bytes());
        }
        i += 1;
    }
    let mut tag = 0;
    while tag < 11 {
        let mut bytes = samples[tag]
            .clone()
            .unwrap_or_else(|| panic!("the negotiation never reached tag {tag}"))
            .to_vec();
        assert!(
            Braid::from_bytes(&bytes).is_ok(),
            "tag {tag} sample does not restore"
        );
        // Version, tag, then the eight epoch bytes.
        bytes[2..10].copy_from_slice(&0u64.to_be_bytes());
        assert!(
            matches!(Braid::from_bytes(&bytes), Err(BraidDecodeError::Malformed)),
            "tag {tag} at epoch zero was restored"
        );
        tag += 1;
    }
    let failed = Braid::from_bytes(&[STATE_VERSION, 11]).unwrap();
    assert!(failed.failed() && failed.invariant());
}

/// The `ct1` clause of `invariant` is stated as an exact length; the bound
/// `BraidT1`'s `State.ct1_bounded` asks for follows from it only while the
/// exact length is within that bound.
#[test]
fn ct1_is_within_the_bound_the_proof_states() {
    const {
        assert!(CT1_LEN <= 4096);
    }
}

/// `invariant` holds after every send and every committed receive of a
/// lossy negotiation and survives a round trip through persistence at every
/// step, on both sides, so what `from_bytes` checks is an inductive
/// invariant of the transitions and not only a shape of the encoding. The
/// same schedule as `from_bytes_refuses_a_field_of_the_wrong_length`, so
/// every live state is visited. `is_initiator` stays what each party was
/// built as, through every swap of sides.
#[test]
fn the_invariant_holds_after_every_step_and_round_trip() {
    let mut r = rng(33);
    let mut p = Pair::new(b"a preshared secret from the handshake");
    let mut seen = [false; 11];
    let mut i = 0usize;
    while i < 1500 {
        let (m, _, _, next) = p.a.send(&mut r);
        assert!(next.invariant(), "initiator after send {i}");
        p.a = next;
        let (_, _, next) = p.b.receive(&m);
        assert!(next.invariant(), "responder after receive {i}");
        p.b.commit(next);
        let (m, _, _, next) = p.b.send(&mut r);
        assert!(next.invariant(), "responder after send {i}");
        p.b = next;
        if i.is_multiple_of(3) {
            let (_, _, next) = p.a.receive(&m);
            assert!(next.invariant(), "initiator after receive {i}");
            p.a.commit(next);
        }
        assert_eq!(p.a.is_initiator(), Some(true), "step {i}");
        assert_eq!(p.b.is_initiator(), Some(false), "step {i}");
        p.a = Braid::from_bytes(&p.a.to_bytes()).unwrap();
        p.b = Braid::from_bytes(&p.b.to_bytes()).unwrap();
        assert!(
            p.a.invariant() && p.b.invariant(),
            "after the round trip at {i}"
        );
        seen[p.a.state_tag() as usize] = true;
        seen[p.b.state_tag() as usize] = true;
        i += 1;
    }
    assert!(!p.a.failed() && !p.b.failed());
    assert!(p.a.epoch() >= 3, "only epoch {} reached", p.a.epoch());
    assert!(
        seen.iter().all(|s| *s),
        "not every live state was visited: {seen:?}"
    );
}

/// The two states that increment the epoch fail closed at the ceiling
/// instead of panicking. The states are built directly, since `from_bytes`
/// now refuses to construct them: this pins the arithmetic itself, so that
/// the decoder's refusal is a second line rather than the only one.
#[test]
fn a_step_from_an_epoch_at_the_ceiling_fails_rather_than_panics() {
    let mut r = rng(30);
    let auth = Auth::init(u64::MAX, b"secret");

    // Transition (13): a message from the next epoch would swap roles.
    let b = Braid {
        state: State::Ct2Sampled {
            epoch: u64::MAX,
            auth: auth.clone(),
            ct2_enc: Encoder::new(&[0u8; CT2_LEN + MAC_LEN]),
        },
    };
    let m = Msg::empty(0);
    let (_, out, next) = b.receive(&m);
    assert!(out.is_none());
    assert!(
        next.failed(),
        "a Ct2Sampled state with no successor epoch must fail closed"
    );
    // Sending from it still does not panic.
    let (_, _, out, _) = b.send(&mut r);
    assert!(out.is_none());

    // Transition (5): the initiator completing an epoch. Driven with a ct2
    // chunk of the right shape; it fails closed before decapsulating.
    let kp = IncrementalKeyPair::generate(&mut r).unwrap();
    let b = Braid {
        state: State::EkSentCt1Received {
            epoch: u64::MAX,
            auth,
            kp,
            ct1: vec![0u8; CT1_LEN],
            ct2_dec: Decoder::new(CT2_LEN + MAC_LEN),
        },
    };
    let mut enc = Encoder::new(&[0u8; CT2_LEN + MAC_LEN]);
    let mut cur = b;
    let mut i = 0;
    while i < 8 && !cur.failed() {
        let m = Msg::with(u64::MAX, MsgType::Ct2, enc.next_chunk());
        let (_, out, next) = cur.receive(&m);
        assert!(out.is_none());
        cur = next;
        i += 1;
    }
    assert!(
        cur.failed(),
        "completing an epoch at the ceiling must fail closed"
    );
}

/// Every restored variable-length field and every restored coder is held to
/// the size its state implies (CR-21, CR-14). Each tag's encoding is taken
/// from a real negotiation, then one field is resized and the decode must
/// answer `Malformed` rather than a state that will fail on its next chunk.
#[test]
fn from_bytes_refuses_a_field_of_the_wrong_length() {
    let mut r = rng(31);
    let mut p = Pair::new(b"a preshared secret from the handshake");

    // Collect one encoding per live tag over a few epochs, from both sides.
    // Two messages in three from `b` are dropped: under strict alternation
    // the acknowledgement always rides on the first `ek_vector` chunk, so
    // `EkReceivedCt1Sampled` (tag 8), where the vector completes before the
    // acknowledgement, is reached only when the other side's `ct1` chunks
    // are being lost. The roles swap each epoch, so the loss reaches both.
    let mut samples: Vec<Option<Zeroizing<Vec<u8>>>> = vec![None; 11];
    let mut i = 0usize;
    while i < 1500 {
        let (m, _, _, next) = p.a.send(&mut r);
        p.a = next;
        Pair::receive_and_commit(&mut p.b, &m);
        let (m, _, _, next) = p.b.send(&mut r);
        p.b = next;
        if i.is_multiple_of(3) {
            Pair::receive_and_commit(&mut p.a, &m);
        }
        let ta = p.a.state_tag() as usize;
        if ta < 11 && samples[ta].is_none() {
            samples[ta] = Some(p.a.to_bytes());
        }
        let tb = p.b.state_tag() as usize;
        if tb < 11 && samples[tb].is_none() {
            samples[tb] = Some(p.b.to_bytes());
        }
        i += 1;
    }
    assert!(!p.a.failed() && !p.b.failed());

    // Walk each encoding's length-prefixed fields after the fixed prefix
    // (version, tag, epoch, auth) and, one at a time, shrink each by one
    // byte. A shrunk KEM field is refused by the KEM's own parser and a shrunk
    // coder by the codec's; the ones this test adds are the plain `Vec`
    // fields and the coder sizes, and every shrink must come back Malformed.
    let mut tag = 0;
    while tag < 11 {
        let bytes = samples[tag]
            .clone()
            .unwrap_or_else(|| panic!("the negotiation never reached tag {tag}"));
        let mut fields = Vec::new();
        let mut pos = 2 + 8 + 64;
        while pos < bytes.len() {
            let (field, next) = take_len_prefixed(&bytes, pos).expect("well-formed sample");
            fields.push((pos, field.len()));
            pos = next;
        }
        let mut f = 0;
        while f < fields.len() {
            let (at, len) = fields[f];
            if len > 0 {
                let mut dirty = Vec::new();
                dirty.extend_from_slice(&bytes[..at]);
                dirty.extend_from_slice(&((len - 1) as u32).to_be_bytes());
                dirty.extend_from_slice(&bytes[at + 4..at + 4 + len - 1]);
                dirty.extend_from_slice(&bytes[at + 4 + len..]);
                assert!(
                    matches!(Braid::from_bytes(&dirty), Err(BraidDecodeError::Malformed)),
                    "tag {tag}, field {f} shortened by one byte was restored"
                );
            }
            f += 1;
        }
        // And the untouched sample still restores, so the refusals above are
        // about the resize and not the sample.
        assert!(
            Braid::from_bytes(&bytes).is_ok(),
            "tag {tag} sample does not restore"
        );
        tag += 1;
    }
}

/// A restored decoder whose declared size is off by one, inside a state whose
/// framing is otherwise exact, is the case the length walk above cannot reach
/// (a decoder's size is inside its own encoding). Built directly.
#[test]
fn from_bytes_refuses_a_decoder_of_the_wrong_size() {
    let b = Braid {
        state: State::NoHeaderReceived {
            epoch: 1,
            auth: Auth::init(1, b"secret"),
            hdr_dec: Decoder::new(HEADER_LEN + MAC_LEN - 1),
        },
    };
    assert!(matches!(
        Braid::from_bytes(&b.to_bytes()),
        Err(BraidDecodeError::Malformed)
    ));
    let honest = Braid::responder(b"secret");
    assert!(Braid::from_bytes(&honest.to_bytes()).is_ok());
}

/// Seeds for the `braid_receive` fuzz target, one per live state and per
/// role: an honest peer's messages up to the first moment the target's own
/// side is parked in that state.
///
/// `fuzz/fuzz_targets/braid_receive.rs` reads a role byte and then messages
/// at a fixed stride, replays each through `receive`, commits the candidate
/// unless it failed, and sends. The target's own randomness is a fixed seed
/// and a fixed secret, and this loop repeats exactly that, so the messages
/// recorded here are ones the target's side will authenticate when replayed.
/// libFuzzer could not discover a MAC-valid header by mutation, which is why
/// the corpus has to be seeded rather than grown (CR-10).
///
/// Ignored by default because it writes into the corpus; run it deliberately
/// when the target's layout or this crate's transitions change:
///
/// ```sh
/// cargo test -p tacenta-braid -- --ignored write_braid_receive_seeds
/// ```
#[test]
#[ignore]
fn write_braid_receive_seeds() {
    // The target's layout: a role byte, then per message 8 epoch, 1 type, 1
    // presence, 2 index, 32 chunk. Kept in step with the target by hand; the
    // target's doc comment names this test.
    fn encode(m: &Msg, out: &mut Vec<u8>) {
        out.extend_from_slice(&m.epoch.to_be_bytes());
        out.push(match m.ty {
            MsgType::None => 0,
            MsgType::Hdr => 1,
            MsgType::Ek => 2,
            MsgType::EkCt1Ack => 3,
            MsgType::Ct1 => 4,
            MsgType::Ct2 => 5,
        });
        match m.data {
            Some(c) => {
                out.push(1);
                out.extend_from_slice(&c.index.to_be_bytes());
                out.extend_from_slice(&c.data);
            }
            None => {
                out.push(0);
                out.extend_from_slice(&[0u8; 2 + CHUNK_SIZE]);
            }
        }
    }

    let dir =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../fuzz/corpus/braid_receive");
    std::fs::create_dir_all(&dir).unwrap();

    let secret = [0x2au8; 32];
    let mut role = 0u8;
    while role < 2 {
        // The target's side, with the target's randomness; the peer with its
        // own, which the target never sees.
        let mut target_rng = rng(0);
        let mut peer_rng = rng(1);
        let (mut target, mut peer) = if role == 0 {
            (Braid::initiator(&secret), Braid::responder(&secret))
        } else {
            (Braid::responder(&secret), Braid::initiator(&secret))
        };
        let mut transcript = vec![role];
        let mut written = [false; 11];
        let write = |tag: u8, transcript: &Vec<u8>, written: &mut [bool; 11]| {
            let t = tag as usize;
            if t < 11 && !written[t] {
                written[t] = true;
                let name = if role == 0 { "initiator" } else { "responder" };
                let path = dir.join(format!("seed-{name}-state-{t:02}.bin"));
                std::fs::write(&path, transcript).unwrap();
                println!("wrote {} ({} bytes)", path.display(), transcript.len());
            }
        };
        write(target.state_tag(), &transcript, &mut written);

        // The first two epochs run without loss, the rest with two of the
        // target's messages in three never reaching the peer. The target's
        // own side is unaffected either way -- it still receives, commits and
        // sends exactly as the fuzz target does -- but the two schedules park
        // it in different states: under strict alternation the
        // acknowledgement arrives before `ek_vector` completes
        // (`Ct1Acknowledged`), and under loss the peer lingers in the state
        // that keeps sending plain `Ek` chunks, so the vector completes first
        // (`EkReceivedCt1Sampled`). The roles swap each epoch, so each
        // schedule gets a responder epoch.
        let mut i = 0usize;
        while i < 6000 {
            let (m, _, _, next) = peer.send(&mut peer_rng);
            peer = next;
            encode(&m, &mut transcript);
            let (_, _, candidate) = target.receive(&m);
            if !candidate.failed() {
                target.commit(candidate);
            }
            write(target.state_tag(), &transcript, &mut written);
            let (m2, _, _, next) = target.send(&mut target_rng);
            target = next;
            write(target.state_tag(), &transcript, &mut written);
            let lossy = target.epoch() >= 3;
            if !lossy || i.is_multiple_of(3) {
                let (_, _, candidate) = peer.receive(&m2);
                peer.commit(candidate);
            }
            i += 1;
        }
        assert!(!target.failed() && !peer.failed());
        let mut t = 0;
        while t < 11 {
            assert!(written[t], "role {role} never parked in state {t}");
            t += 1;
        }
        role += 1;
    }
}
