//! A curve key has one encoding (session-establishment.md, `DecodeEC`). An
//! initial message whose ephemeral key is spelled any other way is refused as a
//! bad encoding, so it cannot pass for a handshake the responder has not seen.

use rand::SeedableRng;
use tacenta_core::sessions::{Identity, LifecycleError, establish_initiator, establish_responder};

/// Offset of the last byte of the ephemeral key in an initial message: version
/// and type, the 33-byte identity encoding, then the ephemeral's curve byte at
/// 35 and its 32 key bytes.
const EPHEMERAL_LAST_BYTE: usize = 2 + 33 + 1 + 31;

#[test]
fn a_last_resort_first_contact_with_a_respelled_ephemeral_is_refused() {
    let mut r = rand::rngs::StdRng::seed_from_u64(7);
    let bob = Identity::generate(&mut r);
    let mut store = bob.create_prekeys(0, &mut r);
    let bundle = store.publish_multi_use();
    let alice = Identity::generate(&mut r);
    let mut session = establish_initiator(&alice, &bundle, &mut r).unwrap();
    let captured = session.encrypt(b"first", &mut r).unwrap();
    assert_eq!(captured[35], 0x05, "the ephemeral's curve byte");
    assert_eq!(
        captured[EPHEMERAL_LAST_BYTE] & 0x80,
        0,
        "an honest key is canonical"
    );

    assert!(establish_responder(&bob, &mut store, &captured, &mut r).is_ok());
    assert!(matches!(
        establish_responder(&bob, &mut store, &captured, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));

    // The same key with bit 255 set names the same point, and is refused.
    let mut respelled = captured.clone();
    respelled[EPHEMERAL_LAST_BYTE] |= 0x80;
    assert!(matches!(
        establish_responder(&bob, &mut store, &respelled, &mut r),
        Err(LifecycleError::BadEncoding)
    ));
    // And refusing it changed nothing: the original is still a replay.
    assert!(matches!(
        establish_responder(&bob, &mut store, &captured, &mut r),
        Err(LifecycleError::ReplayedLastResort)
    ));
}
