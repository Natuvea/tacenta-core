#![allow(unsafe_code)]
#![allow(unsafe_op_in_unsafe_fn)]
#![cfg(feature = "private-erasure-review")]

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use rand::{Rng, SeedableRng};
use tacenta_core::sessions::{Identity, Session, establish_initiator, establish_responder};
use tacenta_spqr::{Output, State};

const MAX_KEYS: usize = 4096;

static ARMED: AtomicBool = AtomicBool::new(false);
static KEY_COUNT: AtomicUsize = AtomicUsize::new(0);
static HITS: AtomicUsize = AtomicUsize::new(0);
static mut KEYS: [[u8; 32]; MAX_KEYS] = [[0; 32]; MAX_KEYS];

struct SecretSpy;

#[global_allocator]
static ALLOCATOR: SecretSpy = SecretSpy;

unsafe impl GlobalAlloc for SecretSpy {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = System.alloc(layout);
        if !ptr.is_null() {
            ptr.write_bytes(0xa5, layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if ARMED.load(Ordering::Acquire) && layout.size() >= 32 {
            let bytes = std::slice::from_raw_parts(ptr.cast_const(), layout.size());
            let count = KEY_COUNT.load(Ordering::Acquire);
            let mut key_index = 0;
            while key_index < count {
                let key = &KEYS[key_index];
                let mut offset = 0;
                while offset + key.len() <= bytes.len() {
                    if bytes[offset..offset + key.len()] == key[..] {
                        HITS.fetch_add(1, Ordering::Relaxed);
                        break;
                    }
                    offset += 1;
                }
                key_index += 1;
            }
        }
        System.dealloc(ptr, layout);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let old_size = layout.size();
        let next = System.realloc(ptr, layout, new_size);
        if !next.is_null() && new_size > old_size {
            next.add(old_size).write_bytes(0xa5, new_size - old_size);
        }
        next
    }
}

fn be32(bytes: &[u8], offset: usize) -> usize {
    u32::from_be_bytes(bytes[offset..offset + 4].try_into().unwrap()) as usize
}

/// Add every SPQR key visible in the public export. The table is populated
/// while the allocator is disarmed; the test deliberately scopes itself to the
/// SPQR state so unrelated session erasure is not conflated with this fix.
unsafe fn record_session_keys(session: &Session, at: &mut usize) {
    let exported = session.export();
    let triple_len = be32(&exported, 1);
    let triple = &exported[5..5 + triple_len];
    let classical_len = be32(triple, 1);

    let mut add = |key: &[u8]| {
        if *at < MAX_KEYS && key.len() == 32 {
            KEYS[*at].copy_from_slice(key);
            *at += 1;
        }
    };

    let pq_offset = 5 + classical_len;
    let pq_len = be32(triple, pq_offset);
    let pq = &triple[pq_offset + 4..pq_offset + 4 + pq_len];
    add(&pq[1..33]);
    let mut pq_offset = 42;
    let chain_count = be32(pq, pq_offset);
    pq_offset += 4;
    for _ in 0..chain_count {
        pq_offset += 8;
        for _ in 0..2 {
            if pq[pq_offset] == 1 {
                add(&pq[pq_offset + 1..pq_offset + 33]);
            }
            pq_offset += 41;
        }
    }
    let pq_skipped_len = be32(pq, pq_offset);
    pq_offset += 4;
    for _ in 0..pq_skipped_len {
        add(&pq[pq_offset + 16..pq_offset + 48]);
        pq_offset += 48;
    }
}

unsafe fn arm_for_sessions(alice: &Session, bob: &Session) {
    let mut count = 0;
    record_session_keys(alice, &mut count);
    record_session_keys(bob, &mut count);
    KEY_COUNT.store(count, Ordering::Release);
    HITS.store(0, Ordering::Release);
    ARMED.store(true, Ordering::Release);
}

#[test]
fn direct_spqr_retirement_wipe_is_mutation_sensitive() {
    tacenta_spqr::review_reset();
    let mut alice = State::init_alice(&[0x11; 32]);
    let mut bob = State::init_bob(&[0x11; 32]);
    let mut sent = Vec::new();
    for _ in 0..4 {
        sent.push(alice.send(0, None).unwrap());
    }
    bob.receive(0, None, sent[3].0).unwrap();
    assert!(
        bob.skipped_len() > 0,
        "fixture did not create a skipped store"
    );
    let o1 = Output::new(1, [0x22; 32]);
    let n1 = alice.send(1, Some(&o1)).unwrap().0;
    bob.receive(1, Some(&o1), n1).unwrap();
    let mut sent = Vec::new();
    for _ in 0..3 {
        sent.push(alice.send(1, None).unwrap());
    }
    bob.receive(1, None, sent[2].0).unwrap();
    let o2 = Output::new(2, [0x33; 32]);
    let n2 = alice.send(2, Some(&o2)).unwrap().0;
    bob.receive(2, Some(&o2), n2).unwrap();
    assert!(!tacenta_spqr::REVIEW_FOUND.load(Ordering::Acquire));
}

#[test]
fn public_session_retirement_wipes_spqr_keys_before_release() {
    tacenta_spqr::review_reset();
    let mut rng = rand::rngs::StdRng::seed_from_u64(43);
    let alice_identity = Identity::generate(&mut rng);
    let bob_identity = Identity::generate(&mut rng);
    let mut store = bob_identity.create_prekeys(0, &mut rng);
    let mut alice =
        establish_initiator(&alice_identity, &store.publish_multi_use(), &mut rng).unwrap();
    let first = alice.encrypt(b"initial", &mut rng).unwrap();
    let (mut bob, _) = establish_responder(&bob_identity, &mut store, &first, &mut rng).unwrap();
    let mut alice_to_bob = Vec::new();
    let mut bob_to_alice = Vec::new();

    for _round in 0..2000 {
        for _ in 0..3 {
            alice_to_bob.push(alice.encrypt(b"a", &mut rng).unwrap());
            bob_to_alice.push(bob.encrypt(b"b", &mut rng).unwrap());
        }
        for _ in 0..3 {
            let index = if alice_to_bob.len() > 90 {
                0
            } else {
                rng.gen_range(0..alice_to_bob.len())
            };
            let message = alice_to_bob.remove(index);
            unsafe { arm_for_sessions(&alice, &bob) };
            let result = bob.decrypt(&message, &mut rng);
            ARMED.store(false, Ordering::Release);
            assert!(result.is_ok());
            assert_eq!(
                HITS.load(Ordering::Acquire),
                0,
                "secret-bearing allocation was released without erasure"
            );
            assert!(!tacenta_spqr::REVIEW_FOUND.load(Ordering::Acquire));
        }
        for _ in 0..3 {
            let index = if bob_to_alice.len() > 90 {
                0
            } else {
                rng.gen_range(0..bob_to_alice.len())
            };
            let message = bob_to_alice.remove(index);
            unsafe { arm_for_sessions(&alice, &bob) };
            let result = alice.decrypt(&message, &mut rng);
            ARMED.store(false, Ordering::Release);
            assert!(result.is_ok());
            assert_eq!(
                HITS.load(Ordering::Acquire),
                0,
                "secret-bearing allocation was released without erasure"
            );
            assert!(!tacenta_spqr::REVIEW_FOUND.load(Ordering::Acquire));
        }
    }
}

#[test]
fn public_session_drop_wipes_spqr_keys_before_release() {
    tacenta_spqr::review_reset();
    let mut rng = rand::rngs::StdRng::seed_from_u64(44);
    let alice_identity = Identity::generate(&mut rng);
    let bob_identity = Identity::generate(&mut rng);
    let mut store = bob_identity.create_prekeys(0, &mut rng);
    let mut alice = Box::new(
        establish_initiator(&alice_identity, &store.publish_multi_use(), &mut rng).unwrap(),
    );
    let first = alice.encrypt(b"initial", &mut rng).unwrap();
    let (bob, _) = establish_responder(&bob_identity, &mut store, &first, &mut rng).unwrap();
    let bob = Box::new(bob);

    unsafe { arm_for_sessions(&alice, &bob) };
    drop(alice);
    ARMED.store(false, Ordering::Release);
    assert_eq!(
        HITS.load(Ordering::Acquire),
        0,
        "dropping a public Session released a secret-bearing allocation"
    );
    assert!(!tacenta_spqr::REVIEW_FOUND.load(Ordering::Acquire));

    tacenta_spqr::review_reset();
    unsafe { arm_for_sessions(&bob, &bob) };
    drop(bob);
    ARMED.store(false, Ordering::Release);
    assert_eq!(
        HITS.load(Ordering::Acquire),
        0,
        "dropping a public Session released a secret-bearing allocation"
    );
    assert!(!tacenta_spqr::REVIEW_FOUND.load(Ordering::Acquire));
}
