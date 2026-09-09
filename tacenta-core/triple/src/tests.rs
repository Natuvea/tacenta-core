//! Fixed stand-ins for keys and Diffie-Hellman outputs, matching the Double
//! Ratchet's own tests: symmetry, `DH(a, B) = DH(b, A)`, is honoured by giving
//! both parties the same output rather than by computing one.

use super::*;

const SK: &[u8] = &[0x01; 32];
const A_PUB: Key = [0x0a; 32];
const B_PUB: Key = [0x0b; 32];
const B2_PUB: Key = [0xb2; 32];
const DH_AB: Key = [0xab; 32];
const DH_B2A: Key = [0xba; 32];

fn out(epoch: u64, byte: u8) -> Output {
    Output::new(epoch, [byte; 32])
}

/// Receive and adopt in one step.
///
/// Real callers must not do this. `receive` hands back a candidate precisely so
/// that the message's authenticator can be checked between deriving the key and
/// moving the state, and these tests have no authenticator: they exercise the
/// ratchet mechanics, and the transaction itself is covered by
/// `nothing_moves_until_a_receive_is_committed` below.
fn receive_and_commit(
    s: &mut State,
    h: &Header,
    dh_recv: &Key,
    dh_send: &Key,
    new_pub: Key,
    o: Option<&Output>,
) -> Result<Key, TripleError> {
    let (next, k) = s.receive(h, dh_recv, dh_send, new_pub, o)?;
    s.commit(next);
    Ok(k)
}

fn alice() -> State {
    State::init_sender(SK, A_PUB, B_PUB, &DH_AB, LabelSet::Tacenta)
}

fn bob() -> State {
    State::init_receiver(SK, B_PUB, LabelSet::Tacenta)
}

#[test]
fn the_two_ratchets_get_different_secrets() {
    // Giving both the same secret would make the hybrid claim false at
    // initialisation, whatever happened afterwards.
    let (ec, pq) = split_secret(SK);
    assert_ne!(ec, pq);
    assert_ne!(&ec[..], SK);
    assert_ne!(&pq[..], SK);
}

#[test]
fn sender_and_receiver_derive_the_same_key() {
    let mut a = alice();
    let mut b = bob();
    let (h, ka) = a.send(0, None).unwrap();
    let kb = receive_and_commit(&mut b, &h, &DH_AB, &DH_B2A, B2_PUB, None).unwrap();
    assert_eq!(ka, kb);
}

#[test]
fn the_combination_is_neither_input() {
    let mk_ec = [0x11u8; 32];
    let mk_pq = [0x22u8; 32];
    let k = combine(&mk_ec, &mk_pq);
    assert_ne!(k, mk_ec);
    assert_ne!(k, mk_pq);
}

#[test]
fn changing_either_input_changes_the_key() {
    // The property the hybrid claim rests on is that the combination cannot be
    // recovered from one input alone, which no test can establish. This is the
    // observable necessary condition: an implementation that ignored one input
    // would satisfy the specification's shape and fail here.
    let base = combine(&[0x11; 32], &[0x22; 32]);

    let mut ec = [0x11u8; 32];
    ec[31] ^= 1;
    assert_ne!(combine(&ec, &[0x22; 32]), base, "classical input ignored");

    let mut pq = [0x22u8; 32];
    pq[31] ^= 1;
    assert_ne!(
        combine(&[0x11; 32], &pq),
        base,
        "post-quantum input ignored"
    );

    // And it is not symmetric, so the two inputs are not interchangeable.
    assert_ne!(combine(&[0x22; 32], &[0x11; 32]), base);
}

#[test]
fn a_conversation_across_epochs() {
    let mut a = alice();
    let mut b = bob();
    let mut epoch = 0u64;
    let mut round = 0;
    while round < 9 {
        // Sparse: a new agreement secret every third message, not every one.
        let o = if round > 0 && round % 3 == 0 {
            epoch += 1;
            Some(out(epoch, epoch as u8))
        } else {
            None
        };
        let (h, ka) = a.send(epoch, o.as_ref()).unwrap();
        assert_eq!(h.epoch, epoch);
        let kb = receive_and_commit(&mut b, &h, &DH_AB, &DH_B2A, B2_PUB, o.as_ref()).unwrap();
        assert_eq!(ka, kb, "round {round}");
        round += 1;
    }
    assert_eq!(a.epoch(), epoch);
    assert_eq!(b.epoch(), epoch);
    assert!(epoch >= 2);
}

#[test]
fn every_message_gets_a_different_key() {
    let mut a = alice();
    let mut keys = Vec::new();
    let mut i = 0;
    while i < 20 {
        let (_, k) = a.send(0, None).unwrap();
        assert!(!keys.contains(&k));
        keys.push(k);
        i += 1;
    }
}

#[test]
fn out_of_order_delivery_still_agrees() {
    let mut a = alice();
    let mut b = bob();
    let mut sent = Vec::new();
    let mut i = 0;
    while i < 5 {
        sent.push(a.send(0, None).unwrap());
        i += 1;
    }
    // Last first, then the rest in reverse: both ratchets store what they pass.
    let mut j = 5;
    while j > 0 {
        j -= 1;
        let (h, ka) = &sent[j];
        let kb = receive_and_commit(&mut b, h, &DH_AB, &DH_B2A, B2_PUB, None).unwrap();
        assert_eq!(*ka, kb, "message {}", j + 1);
    }
}

#[test]
fn a_receiver_cannot_send_before_it_receives() {
    // The Double Ratchet's ordinary transient failure. It must come back as a
    // classical error, and it must leave the post-quantum half untouched, so
    // that the eventual first send is message number one on both.
    let mut b = bob();
    assert!(matches!(b.send(0, None), Err(TripleError::Classical(_))));
    assert!(matches!(b.send(0, None), Err(TripleError::Classical(_))));

    let mut a = alice();
    let (h, _) = a.send(0, None).unwrap();
    receive_and_commit(&mut b, &h, &DH_AB, &DH_B2A, B2_PUB, None).unwrap();

    let (h_b, _) = b.send(0, None).unwrap();
    assert_eq!(h_b.pq_n, 1, "the post-quantum chain moved on a failed send");
    assert_eq!(h_b.dr.n, 0);
}

#[test]
fn an_agreement_secret_for_the_wrong_epoch_is_a_post_quantum_error() {
    let mut a = alice();
    assert!(matches!(
        a.send(7, Some(&out(7, 9))),
        Err(TripleError::PostQuantum(SpqrError::EpochOutOfOrder))
    ));
}

/// A failed send changes nothing, on either half.
///
/// The alternative -- letting the classical half consume the failed send's
/// key -- is not harmless even though the number never reaches the wire: the
/// peer skips it, stores one key it will never spend, and ages it out, so
/// repeated failures raise a peer's skipped-key store without a message ever
/// arriving. Smaller than the receive-side exposure, because a send is driven
/// by our own state rather than by bytes a peer chose, so nobody outside picks
/// the moment. Smaller is not nothing, which is why this pins that the
/// message numbers are consecutive across a failure.
#[test]
fn a_send_that_fails_changes_neither_half() {
    let mut a = alice();
    let mut b = bob();
    let (h1, k1) = a.send(0, None).unwrap();

    // Fails in the post-quantum half, after the classical half has run.
    assert!(a.send(7, Some(&out(7, 9))).is_err());

    let (h2, k2) = a.send(0, None).unwrap();

    // The two halves number messages differently, which is worth pinning: the
    // Double Ratchet numbers from zero, following its specification, and the
    // sparse ratchet from one, because its chain step is keyed by the number it
    // produces and a chain that has produced nothing is at zero.
    assert_eq!(h1.dr.n, 0);
    assert_eq!(h1.pq_n, 1);

    // The point: consecutive, with no gap where the failure was.
    assert_eq!(h2.dr.n, 1, "a failed send consumed a classical message key");
    assert_eq!(h2.pq_n, 2, "a failed send moved the post-quantum half");

    // And both messages still arrive.
    assert_eq!(
        receive_and_commit(&mut b, &h1, &DH_AB, &DH_B2A, B2_PUB, None).unwrap(),
        k1
    );
    assert_eq!(
        receive_and_commit(&mut b, &h2, &DH_AB, &DH_B2A, B2_PUB, None).unwrap(),
        k2
    );
}

#[test]
fn a_tampered_header_number_does_not_yield_the_right_key() {
    let mut a = alice();
    let mut b = bob();
    let (mut h, k) = a.send(0, None).unwrap();
    let _ = a.send(0, None).unwrap();
    h.pq_n += 1;
    // Rejecting it is fine and deriving a different key is fine. Deriving the
    // same key from a header that says something else is not.
    if let Ok(other) = receive_and_commit(&mut b, &h, &DH_AB, &DH_B2A, B2_PUB, None) {
        assert_ne!(other, k, "a moved number produced the same key");
    }
}

/// A receive that is not committed changes nothing, on either half.
///
/// `receive` returns a candidate and the caller commits it only after the
/// ciphertext authenticates. It matters most exactly here: two state machines
/// advance per message, so a header nobody has authenticated would otherwise
/// move twice as much state as a classical session's, and consume the keys of
/// genuine messages still in flight.
#[test]
fn nothing_moves_until_a_receive_is_committed() {
    let mut a = alice();
    let mut b = bob();

    let (h1, k1) = a.send(0, None).unwrap();
    let (h2, k2) = a.send(0, None).unwrap();

    // Derive against the first message repeatedly without committing. If any of
    // it leaked into `b`, the second call would see a moved chain and the third
    // would differ again.
    for _ in 0..8 {
        let (_candidate, k) = b.receive(&h1, &DH_AB, &DH_B2A, B2_PUB, None).unwrap();
        assert_eq!(k, k1, "an uncommitted receive moved the state");
    }

    // The second message still decrypts. Were the derivation committed on a
    // message that never authenticates, the genuine one behind it would lose
    // its key.
    let ka = receive_and_commit(&mut b, &h1, &DH_AB, &DH_B2A, B2_PUB, None).unwrap();
    assert_eq!(ka, k1);
    let kb = receive_and_commit(&mut b, &h2, &DH_AB, &DH_B2A, B2_PUB, None).unwrap();
    assert_eq!(kb, k2);
}

/// A refusal from the post-quantum half leaves the classical half alone.
///
/// Running the classical ratchet first and returning on the post-quantum
/// error would leave a header whose second half was unacceptable having
/// already advanced the first, with nothing to distinguish that from a message
/// that worked.
#[test]
fn a_refusal_on_one_half_does_not_advance_the_other() {
    let mut a = alice();
    let mut b = bob();

    let (h, k) = a.send(0, None).unwrap();

    // A header the post-quantum half will refuse: an epoch it knows nothing of.
    let mut bad = h;
    bad.epoch = 999;
    assert!(b.receive(&bad, &DH_AB, &DH_B2A, B2_PUB, None).is_err());

    // The classical half never moved, so the genuine message still works.
    let got = receive_and_commit(&mut b, &h, &DH_AB, &DH_B2A, B2_PUB, None).unwrap();
    assert_eq!(
        got, k,
        "a rejected header consumed the genuine message's key"
    );
}

/// A state with both halves non-trivially advanced -- several classical
/// messages, an epoch secret folded in, an out-of-order delivery so the
/// classical skipped store holds something -- round-trips byte for byte and
/// keeps working afterward.
#[test]
fn to_bytes_from_bytes_round_trips_a_populated_state() {
    let mut a = alice();
    let mut b = bob();
    a.send(0, None).unwrap();
    let (h1, _) = a.send(1, Some(&out(1, 1))).unwrap();
    let (h2, k2) = a.send(1, None).unwrap();
    // Out of order, so h1's classical key lands in the skipped store.
    receive_and_commit(&mut b, &h2, &DH_AB, &DH_B2A, B2_PUB, Some(&out(1, 1))).unwrap();

    let bytes = b.to_bytes();
    let restored = State::from_bytes(&bytes).unwrap();
    // Encodings rather than states: `State` has no equality, since a derived
    // one would compare key material byte-wise (CR-22). Each half's own tests
    // compare the restored structure field by field.
    assert_eq!(restored.to_bytes().as_slice(), bytes.as_slice());

    // The restored state keeps working: h1 and h0 are still recoverable, and
    // agree with what receiving them on the un-restored original would give.
    let mut restored = restored;
    let k1_restored = receive_and_commit(&mut restored, &h1, &DH_AB, &DH_B2A, B2_PUB, None);
    let mut b2 = b;
    let k1_direct = receive_and_commit(&mut b2, &h1, &DH_AB, &DH_B2A, B2_PUB, None);
    assert_eq!(k1_restored, k1_direct);
    let _ = k2;
}

/// A freshly initialised state -- no epoch secret folded in yet, no skipped
/// keys, no messages sent -- round-trips too.
#[test]
fn to_bytes_from_bytes_round_trips_a_fresh_state() {
    let fresh = alice();
    let bytes = fresh.to_bytes();
    let restored = State::from_bytes(&bytes).unwrap();
    assert_eq!(restored.to_bytes().as_slice(), bytes.as_slice());
}

#[test]
fn from_bytes_rejects_a_foreign_version() {
    let fresh = alice();
    let mut bytes = fresh.to_bytes().to_vec();
    bytes[0] = 0xff;
    assert!(matches!(
        State::from_bytes(&bytes),
        Err(TripleDecodeError::UnknownVersion)
    ));
}

#[test]
fn from_bytes_rejects_a_truncated_buffer() {
    let fresh = alice();
    let bytes = fresh.to_bytes();
    assert!(matches!(
        State::from_bytes(&bytes[..bytes.len() - 1]),
        Err(TripleDecodeError::Malformed) | Err(TripleDecodeError::TooShort)
    ));
}

#[test]
fn from_bytes_rejects_trailing_bytes() {
    let fresh = alice();
    let mut bytes = fresh.to_bytes().to_vec();
    bytes.push(0x00);
    assert!(matches!(
        State::from_bytes(&bytes),
        Err(TripleDecodeError::Malformed)
    ));
}

/// The two verified-zone copies of `take_len_prefixed` must not drift.
///
/// `LABELS.md` explains why there is no shared crate for the leaf zones:
/// each is translated alone, so a construct one cannot express never reaches
/// another. The cost is that this helper exists here and in `tacenta-braid`
/// (and a third time, written with `?`, in the root crate's session
/// persistence, which is outside every leaf and not checked here). Neither
/// copy is public, so this compares the two function bodies as source,
/// comment lines stripped, and pins this crate's copy on a small corpus so
/// its behaviour is fixed as well as its text (CR-35).
#[test]
fn take_len_prefixed_agrees_with_the_braid_copy() {
    fn body(source: &str) -> String {
        let start = source
            .find("fn take_len_prefixed(")
            .expect("the helper is present");
        let rest = &source[start..];
        let end = rest.find("\n}\n").expect("the helper ends") + 3;
        let mut out = String::new();
        for line in rest[..end].lines() {
            let t = line.trim();
            if t.starts_with("//") || t.is_empty() {
                continue;
            }
            out.push_str(t);
            out.push('\n');
        }
        out
    }
    let here = body(include_str!("lib.rs"));
    let braid = body(include_str!("../../braid/src/lib.rs"));
    assert_eq!(here, braid, "the two take_len_prefixed copies have drifted");

    // The behavioural pin, on the copy this crate can call.
    let buf: &[u8] = &[0, 0, 0, 2, 0xaa, 0xbb, 0, 0, 0, 0, 0, 0, 0, 1, 0xcc];
    assert_eq!(take_len_prefixed(buf, 0), Some((&buf[4..6], 6)));
    assert_eq!(take_len_prefixed(buf, 6), Some((&buf[10..10], 10)));
    assert_eq!(take_len_prefixed(buf, 10), Some((&buf[14..15], 15)));
    assert_eq!(take_len_prefixed(buf, 15), None, "no prefix left");
    assert_eq!(take_len_prefixed(buf, 12), None, "a length past the end");
    assert_eq!(take_len_prefixed(buf, 14), None, "a prefix cut short");
    assert_eq!(
        take_len_prefixed(buf, usize::MAX - 2),
        None,
        "a position that would wrap"
    );
    let huge: &[u8] = &[0xff, 0xff, 0xff, 0xff];
    assert_eq!(take_len_prefixed(huge, 0), None, "a length that would wrap");
}

/// Seeds for the `triple_receive` fuzz target: a few honest headers from
/// each side, in the target's stride layout, so the corpus starts from
/// messages the ratchets accept rather than from noise (CR-10).
///
/// Ignored by default because it writes into the corpus; run it deliberately
/// when the target's layout changes:
///
/// ```sh
/// cargo test -p tacenta-triple -- --ignored write_triple_receive_seeds
/// ```
#[test]
#[ignore]
fn write_triple_receive_seeds() {
    // The target's layout: a role byte, then per message 32 dh, 4 pn, 4 n,
    // 8 epoch, 8 pq_n, 1 output presence, 8 output epoch, 32 output key.
    // Kept in step with the target by hand; its doc comment names this test.
    fn encode(h: &Header, o: Option<&Output>, out: &mut Vec<u8>) {
        out.extend_from_slice(&h.dr.dh);
        out.extend_from_slice(&h.dr.pn.to_be_bytes());
        out.extend_from_slice(&h.dr.n.to_be_bytes());
        out.extend_from_slice(&h.epoch.to_be_bytes());
        out.extend_from_slice(&h.pq_n.to_be_bytes());
        match o {
            Some(o) => {
                out.push(1);
                out.extend_from_slice(&o.key_epoch.to_be_bytes());
                out.extend_from_slice(&o.key);
            }
            None => {
                out.push(0);
                out.extend_from_slice(&[0u8; 8 + 32]);
            }
        }
    }
    let dir =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../fuzz/corpus/triple_receive");
    std::fs::create_dir_all(&dir).unwrap();

    // Role 0 drives Bob, who has received Alice's first message; the seed is
    // Alice's next few, with an agreement secret on the third. Role 1 drives
    // Alice after her first send; the seed is Bob's replies.
    let mut a = alice();
    let mut b = bob();
    let (h, _) = a.send(0, None).unwrap();
    receive_and_commit(&mut b, &h, &DH_AB, &DH_B2A, B2_PUB, None).unwrap();

    let mut seed0 = vec![0u8];
    let o = out(1, 0x33);
    let mut i = 0;
    while i < 4 {
        let output = if i == 2 { Some(&o) } else { None };
        let epoch = if i >= 2 { 1 } else { 0 };
        let (h, _) = a.send(epoch, output).unwrap();
        encode(&h, output, &mut seed0);
        i += 1;
    }
    let path = dir.join("seed-responder-honest.bin");
    std::fs::write(&path, &seed0).unwrap();
    println!("wrote {} ({} bytes)", path.display(), seed0.len());

    let mut seed1 = vec![1u8];
    let mut i = 0;
    while i < 3 {
        let (h, _) = b.send(0, None).unwrap();
        encode(&h, None, &mut seed1);
        i += 1;
    }
    let path = dir.join("seed-initiator-honest.bin");
    std::fs::write(&path, &seed1).unwrap();
    println!("wrote {} ({} bytes)", path.display(), seed1.len());
}
