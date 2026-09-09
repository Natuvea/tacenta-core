//! The model in `Model.SparseRatchet` is the oracle for all of this. These
//! check the things a model check cannot reach cheaply: the bounds under
//! pressure, the retirement of old epochs, and that a stored key is spent when
//! it is used.

use super::*;

fn sk() -> Vec<u8> {
    vec![0x01u8; 32]
}

fn out(epoch: u64, byte: u8) -> Output {
    Output::new(epoch, [byte; 32])
}

#[test]
fn in_order_the_sender_and_receiver_derive_the_same_key() {
    let mut a = State::init_alice(&sk());
    let mut b = State::init_bob(&sk());
    let (n, mk_send) = a.send(0, None).unwrap();
    let mk_recv = b.receive(0, None, n).unwrap();
    assert_eq!(mk_send, mk_recv);
}

#[test]
fn the_two_sides_assign_the_chain_keys_oppositely() {
    // If both used the same one, every derivation would still agree and the
    // session would be broken in the other direction with nothing to show it.
    // Two parties on the same side must not agree.
    let mut a1 = State::init_alice(&sk());
    let mut a2 = State::init_alice(&sk());
    let (n, mk_send) = a1.send(0, None).unwrap();
    let mk_recv = a2.receive(0, None, n).unwrap();
    assert_ne!(mk_send, mk_recv);
}

#[test]
fn a_whole_chain_in_order() {
    let mut a = State::init_alice(&sk());
    let mut b = State::init_bob(&sk());
    let mut i = 0;
    while i < 50 {
        let (n, mk) = a.send(0, None).unwrap();
        assert_eq!(n, i + 1);
        assert_eq!(b.receive(0, None, n).unwrap(), mk);
        i += 1;
    }
    assert_eq!(b.skipped_len(), 0);
}

#[test]
fn an_epoch_secret_opens_new_chains_on_both_sides() {
    let mut a = State::init_alice(&sk());
    let mut b = State::init_bob(&sk());
    let o = out(1, 0xAA);
    let (n, mk) = a.send(1, Some(&o)).unwrap();
    assert_eq!(a.epoch(), 1);
    assert_eq!(b.receive(1, Some(&o), n).unwrap(), mk);
    assert_eq!(b.epoch(), 1);
}

#[test]
fn an_epoch_out_of_order_is_rejected() {
    let mut a = State::init_alice(&sk());
    // The current epoch is 0, so only 1 follows it.
    assert_eq!(a.send(2, Some(&out(2, 1))), Err(SpqrError::EpochOutOfOrder));
    assert_eq!(a.send(0, Some(&out(0, 1))), Err(SpqrError::EpochOutOfOrder));
    // And the state is unchanged by a rejection.
    assert_eq!(a.epoch(), 0);
    assert!(a.send(0, None).is_ok());
}

#[test]
fn out_of_order_delivery_is_recovered_from_the_store() {
    let mut a = State::init_alice(&sk());
    let mut b = State::init_bob(&sk());
    let mut sent = Vec::new();
    let mut i = 0;
    while i < 10 {
        sent.push(a.send(0, None).unwrap());
        i += 1;
    }
    // Deliver the tenth first: nine keys get stored.
    let (n10, mk10) = sent[9];
    assert_eq!(b.receive(0, None, n10).unwrap(), mk10);
    assert_eq!(b.skipped_len(), 9);
    // Then the rest, in reverse, each spending its stored key.
    let mut j = 9;
    while j > 0 {
        j -= 1;
        let (n, mk) = sent[j];
        assert_eq!(b.receive(0, None, n).unwrap(), mk);
    }
    assert_eq!(b.skipped_len(), 0);
}

#[test]
fn a_stored_key_is_spent_when_it_is_used() {
    let mut a = State::init_alice(&sk());
    let mut b = State::init_bob(&sk());
    let (n1, _) = a.send(0, None).unwrap();
    let (n2, mk2) = a.send(0, None).unwrap();
    assert_eq!(b.receive(0, None, n2).unwrap(), mk2);
    assert_eq!(b.skipped_len(), 1);
    assert!(b.receive(0, None, n1).is_ok());
    assert_eq!(b.skipped_len(), 0);
    // A replay finds nothing stored, and the chain has moved past it.
    assert_eq!(b.receive(0, None, n1), Err(SpqrError::OutOfOrder));
}

#[test]
fn a_message_numbered_zero_is_rejected_rather_than_wrapping() {
    // The model subtracts on Nat, where zero minus one is zero. Rust would
    // wrap to u64::MAX and ask to skip eighteen quintillion keys, which the
    // skip bound would then reject with the wrong reason. Saturating gives the
    // model's behaviour, and the request is refused as an ordering failure.
    let mut b = State::init_bob(&sk());
    assert_eq!(b.receive(0, None, 0), Err(SpqrError::OutOfOrder));
    assert_eq!(b.skipped_len(), 0);
}

#[test]
fn skipping_beyond_the_bound_is_refused() {
    let mut b = State::init_bob(&sk());
    assert_eq!(
        b.receive(0, None, MAX_SKIP + 2),
        Err(SpqrError::TooManySkipped)
    );
    // Exactly at the bound is allowed.
    assert!(b.receive(0, None, MAX_SKIP + 1).is_ok());
}

#[test]
fn the_store_bound_stops_repeated_skipping_on_one_chain() {
    // The per-chain bound limits how far a single request may skip, not how
    // much a chain may accumulate. A peer can jump MAX_SKIP forward, then do it
    // again, and again. Without a total bound the store grows without limit on
    // one chain in one epoch, from a peer who never has to send anything real.
    //
    // This is the attack the divergence exists for, and it is sharper than
    // the cross-epoch growth the divergence also bounds.
    let mut b = State::init_bob(&sk());
    b.receive(0, None, MAX_SKIP + 1).unwrap();
    assert_eq!(b.skipped_len(), MAX_SKIP as usize);
    b.receive(0, None, 2 * (MAX_SKIP + 1)).unwrap();
    assert_eq!(b.skipped_len(), 2 * MAX_SKIP as usize);
    assert_eq!(
        b.receive(0, None, 3 * (MAX_SKIP + 1)),
        Err(SpqrError::SkippedStoreFull)
    );
    assert!(b.skipped_len() <= MAX_SKIPPED_STORE);
}

#[test]
fn retirement_keeps_the_cross_epoch_total_below_the_bound() {
    // Skipping the maximum in every epoch does not accumulate, because
    // retirement drops everything older than EPOCHS_KEPT. So the total stays at
    // or under MAX_SKIP * EPOCHS_KEPT, which is exactly MAX_SKIPPED_STORE.
    //
    // Worth pinning: it says the two bounds are consistent rather than
    // accidentally in tension, and it says which one is doing the work in which
    // situation.
    let mut b = State::init_bob(&sk());
    let mut epoch = 0u64;
    let mut i = 0;
    while i < 10 {
        epoch += 1;
        let o = out(epoch, epoch as u8);
        b.receive(epoch, Some(&o), MAX_SKIP + 1).unwrap();
        assert!(
            b.skipped_len() <= MAX_SKIP as usize * EPOCHS_KEPT as usize,
            "epoch {epoch} held {}",
            b.skipped_len()
        );
        i += 1;
    }
    assert_eq!(MAX_SKIPPED_STORE, MAX_SKIP as usize * EPOCHS_KEPT as usize);
}

#[test]
fn old_epochs_are_retired() {
    let mut b = State::init_bob(&sk());
    // Skip some keys in epoch 1 so there is something to retire.
    let o1 = out(1, 1);
    b.receive(1, Some(&o1), 5).unwrap();
    assert_eq!(b.skipped_len(), 4);

    // Two more epochs, and epoch 1 falls outside EPOCHS_KEPT.
    let o2 = out(2, 2);
    let o3 = out(3, 3);
    b.receive(2, Some(&o2), 1).unwrap();
    assert_eq!(b.skipped_len(), 4);
    b.receive(3, Some(&o3), 1).unwrap();
    assert_eq!(b.skipped_len(), 0, "epoch 1's stored keys outlived it");

    // And its chains are gone with them, so a late message for it is refused
    // rather than decrypted.
    assert_eq!(b.receive(1, None, 6), Err(SpqrError::NoChain));
}

#[test]
fn a_retired_epoch_cannot_be_sent_on() {
    let mut a = State::init_alice(&sk());
    let o1 = out(1, 1);
    let o2 = out(2, 2);
    a.send(1, Some(&o1)).unwrap();
    a.send(2, Some(&o2)).unwrap();
    assert!(
        a.send(1, None).is_ok(),
        "epoch 1 is still within the window"
    );
    let o3 = out(3, 3);
    a.send(3, Some(&o3)).unwrap();
    assert_eq!(a.send(1, None), Err(SpqrError::NoChain));
}

#[test]
fn a_full_conversation_across_several_epochs() {
    let mut a = State::init_alice(&sk());
    let mut b = State::init_bob(&sk());
    let mut epoch = 0u64;
    let mut round = 0;
    while round < 12 {
        // Every third round the agreement lands a new secret, which is what
        // "sparse" means: chains carry many messages between epochs.
        let advance = round % 3 == 0 && round > 0;
        let o = if advance {
            epoch += 1;
            Some(out(epoch, epoch as u8))
        } else {
            None
        };
        let (n, mk) = a.send(epoch, o.as_ref()).unwrap();
        assert_eq!(b.receive(epoch, o.as_ref(), n).unwrap(), mk);

        // And back the other way on the same epoch's other chain.
        let (n, mk) = b.send(epoch, None).unwrap();
        assert_eq!(a.receive(epoch, None, n).unwrap(), mk);
        round += 1;
    }
    assert_eq!(a.epoch(), epoch);
    assert_eq!(b.epoch(), epoch);
    assert!(epoch >= 3);
}

#[test]
fn a_secret_for_the_wrong_epoch_does_not_disturb_the_state() {
    let mut a = State::init_alice(&sk());
    let (n1, mk1) = a.send(0, None).unwrap();
    assert_eq!(a.send(5, Some(&out(5, 9))), Err(SpqrError::EpochOutOfOrder));
    // The sending chain did not move: the next message is still number two.
    let (n2, _) = a.send(0, None).unwrap();
    assert_eq!(n1, 1);
    assert_eq!(n2, 2);
    let mut b = State::init_bob(&sk());
    assert_eq!(b.receive(0, None, 1).unwrap(), mk1);
}

/// A state with populated chains and skipped stores across several epochs
/// round-trips byte for byte and field for field, and keeps working
/// afterward.
#[test]
fn to_bytes_from_bytes_round_trips_a_populated_state() {
    let mut a = State::init_alice(&sk());
    let mut b = State::init_bob(&sk());
    let o1 = out(1, 1);
    // A whole chain, an epoch advance, and an out-of-order delivery so both
    // the chains vector and the skipped store are non-trivial.
    a.send(0, None).unwrap();
    let (n1, _) = a.send(1, Some(&o1)).unwrap();
    let (n2, _) = a.send(1, None).unwrap();
    b.receive(1, Some(&o1), n2).unwrap();
    assert_eq!(b.skipped_len(), 1, "n1's key is still in the store");

    let bytes = b.to_bytes();
    let restored = State::from_bytes(&bytes).unwrap();
    assert_eq!(b, restored);

    // The restored state keeps working: n1 is still recoverable from it, and
    // it agrees with a fresh receive on the un-restored original.
    let mut restored = restored;
    let mk1_restored = restored.receive(1, None, n1).unwrap();
    let mut b2 = b;
    let mk1_direct = b2.receive(1, None, n1).unwrap();
    assert_eq!(mk1_restored, mk1_direct);
}

/// A freshly initialised state has one chains entry, an empty skipped store,
/// and no optional chain retired yet -- the other end of the shape
/// `to_bytes` encodes.
#[test]
fn to_bytes_from_bytes_round_trips_a_fresh_state() {
    let fresh = State::init_alice(&sk());
    let bytes = fresh.to_bytes();
    let restored = State::from_bytes(&bytes).unwrap();
    assert_eq!(fresh, restored);
}

#[test]
fn from_bytes_rejects_a_foreign_version() {
    let fresh = State::init_alice(&sk());
    let mut bytes = fresh.to_bytes().to_vec();
    bytes[0] = 0xff;
    assert_eq!(
        State::from_bytes(&bytes),
        Err(SpqrDecodeError::UnknownVersion)
    );
}

#[test]
fn from_bytes_rejects_a_truncated_buffer() {
    let fresh = State::init_alice(&sk());
    let bytes = fresh.to_bytes();
    assert_eq!(
        State::from_bytes(&bytes[..bytes.len() - 1]),
        Err(SpqrDecodeError::TooShort)
    );
}

#[test]
fn from_bytes_rejects_a_bad_chain_presence_byte() {
    let fresh = State::init_alice(&sk());
    let mut bytes = fresh.to_bytes().to_vec();
    // version(1) + rk(32) + epoch(8) + direction(1) + chains_count(4) + epoch
    // key(8) lands on the send chain's presence byte.
    bytes[1 + 32 + 8 + 1 + 4 + 8] = 0x02;
    assert_eq!(State::from_bytes(&bytes), Err(SpqrDecodeError::Malformed));
}

#[test]
fn from_bytes_rejects_trailing_bytes() {
    let fresh = State::init_alice(&sk());
    let mut bytes = fresh.to_bytes().to_vec();
    bytes.push(0x00);
    assert_eq!(State::from_bytes(&bytes), Err(SpqrDecodeError::Malformed));
}

/// An absent chain's forty bytes must be zero. Marking a present chain absent
/// leaves its key and counter in the padding; decoding that as "absent" and
/// re-encoding it as zeros would be two spellings of one state, which the
/// persisted-state fuzz target's re-encode oracle checks for.
#[test]
fn from_bytes_rejects_nonzero_padding_in_an_absent_chain() {
    let fresh = State::init_alice(&sk());
    let mut bytes = fresh.to_bytes().to_vec();
    let presence = 1 + 32 + 8 + 1 + 4 + 8;
    assert_eq!(bytes[presence], 0x01, "the fresh send chain is present");
    bytes[presence] = 0x00;
    assert_eq!(State::from_bytes(&bytes), Err(SpqrDecodeError::Malformed));

    // With the padding zeroed as well, the absent spelling is canonical and
    // decodes.
    for b in &mut bytes[presence + 1..presence + 1 + 32 + 8] {
        *b = 0;
    }
    let restored = State::from_bytes(&bytes).unwrap();
    assert_eq!(restored.to_bytes().as_slice(), bytes.as_slice());
}

/// The layout `to_bytes` writes: version, rk, epoch and direction, then the
/// chains count and entries, then the skipped count and entries.
const EPOCH_AT: usize = 1 + 32;
const CHAINS_COUNT_AT: usize = 1 + 32 + 8 + 1;
const CHAINS_AT: usize = CHAINS_COUNT_AT + 4;
const CHAINS_ENTRY_LEN: usize = 8 + (1 + 32 + 8) * 2;
const SKIPPED_ENTRY_LEN: usize = 8 + 8 + 32;

/// A state one epoch in, so its chains vector holds two entries (epochs
/// zero and one) and every window clause has room to be violated.
fn advanced_once() -> State {
    let mut a = State::init_alice(&sk());
    a.send(1, Some(&out(1, 1))).unwrap();
    assert_eq!(a.epoch(), 1);
    a
}

/// Two `chains` entries for one epoch are refused (CR-21). `find_chains`
/// would answer with the first and `set_chains` would remove both, so the
/// state is one no honest run produces and the two would disagree about
/// which chains are live.
#[test]
fn from_bytes_rejects_a_duplicated_epoch_entry() {
    let a = advanced_once();
    let bytes = a.to_bytes();
    assert!(State::from_bytes(&bytes).is_ok());
    // Two entries, epochs zero and one; relabel the second as zero.
    let second = CHAINS_AT + CHAINS_ENTRY_LEN;
    let mut dirty = bytes.to_vec();
    dirty[second..second + 8].copy_from_slice(&0u64.to_be_bytes());
    assert!(matches!(
        State::from_bytes(&dirty),
        Err(SpqrDecodeError::Malformed)
    ));
}

/// A chains entry the window does not cover is refused (`State::invariant`):
/// one for an epoch past the current, which `advance` never opens, and one
/// too old, which `clear_old_epochs` would have retired.
#[test]
fn from_bytes_rejects_a_chains_entry_outside_the_window() {
    let fresh = State::init_alice(&sk());
    let mut ahead = fresh.to_bytes().to_vec();
    ahead[CHAINS_AT..CHAINS_AT + 8].copy_from_slice(&1u64.to_be_bytes());
    assert!(matches!(
        State::from_bytes(&ahead),
        Err(SpqrDecodeError::Malformed)
    ));

    // At epoch two the window holds epochs one and two; relabel the older
    // entry as zero, which the advance to two retired.
    let mut a = advanced_once();
    a.send(2, Some(&out(2, 2))).unwrap();
    let bytes = a.to_bytes();
    assert!(State::from_bytes(&bytes).is_ok());
    let count = u32::from_be_bytes(bytes[CHAINS_COUNT_AT..CHAINS_AT].try_into().unwrap());
    assert_eq!(count, 2, "epochs one and two are kept");
    let mut stale = bytes.to_vec();
    let mut i = 0;
    while i < 2 {
        let at = CHAINS_AT + i * CHAINS_ENTRY_LEN;
        if stale[at..at + 8] == 1u64.to_be_bytes() {
            stale[at..at + 8].copy_from_slice(&0u64.to_be_bytes());
        }
        i += 1;
    }
    assert!(matches!(
        State::from_bytes(&stale),
        Err(SpqrDecodeError::Malformed)
    ));
}

/// A state whose current epoch has no chains entry is refused
/// (`State::invariant`): `init` and `advance` both open the current epoch's
/// chains, and nothing retires them while the epoch is current.
#[test]
fn from_bytes_rejects_a_current_epoch_without_chains() {
    let fresh = State::init_alice(&sk());
    let mut bytes = fresh.to_bytes().to_vec();
    // Epoch one, with only epoch zero's chains: inside the window, but the
    // current epoch has nothing to send or receive on.
    bytes[EPOCH_AT..EPOCH_AT + 8].copy_from_slice(&1u64.to_be_bytes());
    assert!(matches!(
        State::from_bytes(&bytes),
        Err(SpqrDecodeError::Malformed)
    ));
}

/// A store past `MAX_SKIPPED_STORE` is refused (`State::invariant`), even
/// with a buffer large enough to hold it; at the bound it restores.
#[test]
fn from_bytes_rejects_a_store_past_its_bound() {
    let fresh = State::init_alice(&sk());
    let bytes = fresh.to_bytes();
    let skipped_count_at = CHAINS_AT + CHAINS_ENTRY_LEN;
    let with = |count: usize| {
        let mut dirty = Vec::new();
        dirty.extend_from_slice(&bytes[..skipped_count_at]);
        dirty.extend_from_slice(&(count as u32).to_be_bytes());
        let mut n = 0u64;
        while (n as usize) < count {
            // Every key under epoch zero, distinct by number.
            dirty.extend_from_slice(&0u64.to_be_bytes());
            dirty.extend_from_slice(&(n + 1).to_be_bytes());
            dirty.extend_from_slice(&[0u8; 32]);
            n += 1;
        }
        dirty
    };
    assert!(matches!(
        State::from_bytes(&with(MAX_SKIPPED_STORE + 1)),
        Err(SpqrDecodeError::Malformed)
    ));
    let restored = State::from_bytes(&with(MAX_SKIPPED_STORE)).unwrap();
    assert_eq!(restored.skipped_len(), MAX_SKIPPED_STORE);
    assert!(restored.invariant());
}

/// A stored key repeated under one `(epoch, n)` is refused, and so is one
/// under an epoch with no chains entry (`State::invariant`): the first is
/// unreachable by `try_skipped`, the second is one `clear_old_epochs` would
/// have retired with its chains.
#[test]
fn from_bytes_rejects_a_stored_key_the_operations_could_not_have_left() {
    let mut a = State::init_alice(&sk());
    let mut b = State::init_bob(&sk());
    a.send(0, None).unwrap();
    let (n2, _) = a.send(0, None).unwrap();
    b.receive(0, None, n2).unwrap();
    assert_eq!(b.skipped_len(), 1);
    let bytes = b.to_bytes();
    let skipped_count_at = CHAINS_AT + CHAINS_ENTRY_LEN;
    let entry_at = skipped_count_at + 4;

    let mut twice = Vec::new();
    twice.extend_from_slice(&bytes[..skipped_count_at]);
    twice.extend_from_slice(&2u32.to_be_bytes());
    twice.extend_from_slice(&bytes[entry_at..]);
    twice.extend_from_slice(&bytes[entry_at..]);
    assert!(matches!(
        State::from_bytes(&twice),
        Err(SpqrDecodeError::Malformed)
    ));
    // The same two entries with distinct numbers restore.
    let second_n = entry_at + SKIPPED_ENTRY_LEN + 8;
    twice[second_n..second_n + 8].copy_from_slice(&7u64.to_be_bytes());
    assert!(State::from_bytes(&twice).is_ok());

    let mut retired = bytes.to_vec();
    retired[entry_at..entry_at + 8].copy_from_slice(&5u64.to_be_bytes());
    assert!(matches!(
        State::from_bytes(&retired),
        Err(SpqrDecodeError::Malformed)
    ));
}

/// `invariant` holds after every send and receive of a conversation with
/// out-of-order delivery, losses, stored keys spent later and several epoch
/// advances, and survives a round trip through persistence at every step,
/// so what `from_bytes` checks is an inductive invariant of the operations
/// and not only a shape of the encoding. The message keys still agree, so
/// the states driven are ones a working session holds.
#[test]
fn the_invariant_holds_after_every_step_and_round_trip() {
    let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut a = State::init_alice(&sk());
    let mut b = State::init_bob(&sk());
    assert!(a.invariant() && b.invariant());
    assert_eq!(a.direction(), Direction::A2b);
    assert_eq!(b.direction(), Direction::B2a);
    // Keys dropped on the way to each party, to be delivered later.
    let mut backlog_a: Vec<(u64, u64, Key)> = Vec::new();
    let mut backlog_b: Vec<(u64, u64, Key)> = Vec::new();
    let mut epoch = 0u64;
    let mut delivered = 0;
    let mut found_later = 0;
    let mut round = 0;
    while round < 60 {
        let (sender, receiver, backlog_s, backlog_r) = if round % 2 == 0 {
            (&mut a, &mut b, &mut backlog_a, &mut backlog_b)
        } else {
            (&mut b, &mut a, &mut backlog_b, &mut backlog_a)
        };
        // Spend some stored keys first, while their epoch is still kept.
        while !backlog_s.is_empty() && next() % 3 != 0 {
            let (e, n, mk) = backlog_s.remove(0);
            if e + EPOCHS_KEPT > sender.epoch() {
                assert_eq!(
                    sender.receive(e, None, n).unwrap(),
                    mk,
                    "a stored key in round {round}"
                );
                assert!(sender.invariant(), "after a stored key in round {round}");
                found_later += 1;
            }
        }
        // Every third round the agreement yields the next epoch's secret,
        // folded in on the first message of the round by both sides.
        let mut secret = None;
        if round % 3 == 2 {
            epoch += 1;
            secret = Some(out(epoch, epoch as u8));
        }
        let count = 1 + (next() % 12) as usize;
        let mut sent = Vec::new();
        let mut i = 0;
        while i < count {
            let o = if i == 0 { secret.as_ref() } else { None };
            let (n, mk) = sender.send(epoch, o).unwrap();
            assert!(sender.invariant(), "sender after send {i} of round {round}");
            sent.push((n, mk));
            i += 1;
        }
        let mut highest = 0;
        let mut dropped = Vec::new();
        let mut i = 0;
        while i < count {
            let pick = (next() as usize) % sent.len();
            let (n, mk) = sent.remove(pick);
            if i == 0 || next() % 4 != 0 {
                let o = if i == 0 { secret.as_ref() } else { None };
                assert_eq!(
                    receiver.receive(epoch, o, n).unwrap(),
                    mk,
                    "message {i} of round {round}"
                );
                assert!(
                    receiver.invariant(),
                    "receiver after receive {i} of round {round}"
                );
                if n > highest {
                    highest = n;
                }
                delivered += 1;
            } else {
                dropped.push((n, mk));
            }
            i += 1;
        }
        let mut i = 0;
        while i < dropped.len() {
            if dropped[i].0 < highest {
                backlog_r.push((epoch, dropped[i].0, dropped[i].1));
            }
            i += 1;
        }
        *sender = State::from_bytes(&sender.to_bytes()).unwrap();
        *receiver = State::from_bytes(&receiver.to_bytes()).unwrap();
        assert!(
            sender.invariant() && receiver.invariant(),
            "after the round trip of round {round}"
        );
        round += 1;
    }
    assert!(epoch >= 15, "only {epoch} epochs");
    assert!(delivered >= 200, "only {delivered} messages delivered");
    assert!(
        found_later >= 10,
        "only {found_later} stored keys were spent"
    );
}
