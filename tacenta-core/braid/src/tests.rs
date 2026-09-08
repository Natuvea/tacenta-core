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
