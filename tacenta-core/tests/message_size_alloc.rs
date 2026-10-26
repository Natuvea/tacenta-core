//! The size refusals copy nothing (tacenta-spec/protocol/message-format.md, Message size: the size rule runs
//! "before the frame is copied or decoded"). **Tested only, on the inputs below.**
//!
//! A counting global allocator records the bytes allocated while it is armed. Armed around a refused call,
//! it must record less than one kilobyte, for frames of a megabyte. Armed around an admitted frame of the
//! same size, it must record at least the frame's length, which shows the spy sees the copy the refusal
//! avoids. A refusal moved after `message.to_vec()` or after `decode_initial` in `Session::decrypt`, or after
//! `decode_initial` in `establish_responder`, fails here; nothing else in the tests can see it, because such
//! a refusal has the same result and effects.
//!
//! One test, so that no other test in this binary allocates while the spy is armed.

#![allow(unsafe_code)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use rand::SeedableRng;
use tacenta_core::serialization::{
    DecodeError, MAX_INITIAL_FRAME_LEN, MAX_PLAINTEXT_LEN, MAX_RATCHET_FRAME_LEN, decode_initial,
    encode_initial,
};
use tacenta_core::sessions::{
    self, Expectation, LifecycleError, establish_initiator, establish_responder,
};

static ARMED: AtomicBool = AtomicBool::new(false);
static ALLOCATED: AtomicUsize = AtomicUsize::new(0);

struct Counting;

#[global_allocator]
static ALLOCATOR: Counting = Counting;

// SAFETY: every call is forwarded to `System` unchanged; the counter is only an atomic add.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if ARMED.load(Ordering::Acquire) {
            ALLOCATED.fetch_add(layout.size(), Ordering::AcqRel);
        }
        // SAFETY: the caller's contract is `System`'s.
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if ARMED.load(Ordering::Acquire) {
            ALLOCATED.fetch_add(layout.size(), Ordering::AcqRel);
        }
        // SAFETY: as above.
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if ARMED.load(Ordering::Acquire) {
            ALLOCATED.fetch_add(new_size, Ordering::AcqRel);
        }
        // SAFETY: as above.
        unsafe { System.realloc(ptr, layout, new_size) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: as above.
        unsafe { System.dealloc(ptr, layout) }
    }
}

/// Run `f` with the spy armed and return the bytes allocated meanwhile.
fn allocated_during<T>(f: impl FnOnce() -> T) -> (T, usize) {
    ALLOCATED.store(0, Ordering::Release);
    ARMED.store(true, Ordering::Release);
    let out = f();
    ARMED.store(false, Ordering::Release);
    (out, ALLOCATED.load(Ordering::Acquire))
}

const TOO_LONG: LifecycleError = LifecycleError::Decode(DecodeError::TooLong);
const SMALL: usize = 1024;

#[test]
fn size_refusals_allocate_nothing_proportional_to_the_frame() {
    let mut r = rand::rngs::StdRng::seed_from_u64(21);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);
    let bundle = bob_prekeys.publish();
    let mut alice =
        establish_initiator(&alice_id, &bundle, &Expectation::first_contact(&[]), &mut r).unwrap();
    let first = alice.encrypt(b"first", &mut r).unwrap();
    let (mut bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &first, &mut r).unwrap();

    // A ratchet-type frame one over the ratchet bound.
    let mut ratchet = vec![0u8; MAX_RATCHET_FRAME_LEN + 1];
    ratchet[0] = 0x01;
    ratchet[1] = 0x01;
    let (result, bytes) = allocated_during(|| bob.decrypt(&ratchet, &mut r));
    assert_eq!(result, Err(TOO_LONG));
    assert!(
        bytes < SMALL,
        "a refused ratchet frame allocated {bytes} bytes"
    );

    // A repeat of Alice's handshake, re-wrapped with an empty KEM ciphertext around a ratchet message one
    // over the bound: an initial frame the decoder would accept, refused before it runs.
    let repeat = alice.encrypt(b"repeat", &mut r).unwrap();
    let d = decode_initial(&repeat).unwrap();
    let mut inner = d.message.clone();
    inner.resize(MAX_RATCHET_FRAME_LEN + 1, 0);
    let nested = encode_initial(
        &d.identity,
        &d.ephemeral,
        &[],
        d.signed_prekey_id,
        d.one_time_prekey_id,
        d.kem_prekey_id,
        &inner,
    );
    drop(inner);
    let (result, bytes) = allocated_during(|| bob.decrypt(&nested, &mut r));
    assert_eq!(result, Err(TOO_LONG));
    assert!(
        bytes < SMALL,
        "a refused nested frame allocated {bytes} bytes on the session"
    );
    let (result, bytes) =
        allocated_during(|| establish_responder(&bob_id, &mut bob_prekeys, &nested, &mut r).err());
    assert_eq!(result, Some(TOO_LONG));
    assert!(
        bytes < SMALL,
        "a refused nested frame allocated {bytes} bytes on establishment"
    );

    // An initial frame one over the outer bound.
    let mut outer = repeat.clone();
    outer.resize(MAX_INITIAL_FRAME_LEN + 1, 0);
    let (result, bytes) = allocated_during(|| bob.decrypt(&outer, &mut r));
    assert_eq!(result, Err(TOO_LONG));
    assert!(
        bytes < SMALL,
        "a refused outer frame allocated {bytes} bytes"
    );
    let (result, bytes) =
        allocated_during(|| establish_responder(&bob_id, &mut bob_prekeys, &outer, &mut r).err());
    assert_eq!(result, Some(TOO_LONG));
    assert!(
        bytes < SMALL,
        "a refused outer frame allocated {bytes} bytes on establishment"
    );

    // A plaintext one over the sender's bound.
    let plaintext = vec![0u8; MAX_PLAINTEXT_LEN + 1];
    let (result, bytes) = allocated_during(|| alice.encrypt(&plaintext, &mut r));
    assert_eq!(result, Err(LifecycleError::PlaintextTooLong));
    assert!(bytes < SMALL, "a refused plaintext allocated {bytes} bytes");

    // The control: the same session copies an admitted frame of the bound's size, which the spy sees.
    ratchet.truncate(MAX_RATCHET_FRAME_LEN);
    let (result, bytes) = allocated_during(|| bob.decrypt(&ratchet, &mut r));
    assert!(result.is_err(), "the zero-filled frame does not decode");
    assert!(
        bytes >= MAX_RATCHET_FRAME_LEN,
        "the spy did not see the copy of an admitted frame ({bytes} bytes)"
    );
    let mut admitted = repeat.clone();
    admitted.resize(MAX_INITIAL_FRAME_LEN, 0);
    let (_, bytes) = allocated_during(|| {
        establish_responder(&bob_id, &mut bob_prekeys, &admitted, &mut r).err()
    });
    assert!(
        bytes >= MAX_RATCHET_FRAME_LEN,
        "the spy did not see establishment's copy of an admitted frame ({bytes} bytes)"
    );
}
