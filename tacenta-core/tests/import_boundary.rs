//! The persisted-state trust boundary, exercised where untrusted bytes arrive.
//!
//! `Session::import` is the single point every persisted session in the product
//! passes through: the session restore path calls it once per session. The
//! nested decoders
//! live in the verified crates and are deliberately unchanged, so this check
//! costs no proof work.

use rand::SeedableRng;
use tacenta_core::sessions::{self, Session, SessionDecodeError, establish_initiator};

/// A real, established session: PQXDH plus the first ratchet step. Built the
/// same way `benchmarks.rs` builds one, so this exercises the shape a product
/// actually persists rather than a freshly initialised skeleton.
fn an_established_session() -> Session {
    let mut r = rand::rngs::StdRng::seed_from_u64(7);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let bob_prekeys = bob_id.create_prekeys(32, &mut r);
    let bundle = bob_prekeys.publish();
    establish_initiator(&alice_id, &bundle, &mut r).expect("establishment must succeed")
}

/// Round-tripping an ordinary session must still work. Without this the
/// canonicity check could pass by refusing everything.
#[test]
fn an_exported_session_still_imports() {
    let session = an_established_session();
    let bytes = session.export();
    let back = Session::import(&bytes).expect("our own export must import");
    assert_eq!(back.export().as_slice(), bytes.as_slice());
}

/// **The shape under test.** An absent optional key encodes as a presence byte
/// plus 32 bytes of padding. A nested decoder that returned `None` without
/// reading the padding would decode such a byte string to a state whose
/// re-encoding differed from it, and `Session::import` would refuse it by
/// re-encoding and comparing.
///
/// **The nested decoders refuse that padding themselves**
/// (`tacenta-ratchet`'s `read_optional_key`, `tacenta-spqr`'s `decode_chain`),
/// and the persisted-state fuzz target's re-encode oracle checks the same
/// thing. So the session-level check is a backstop that no single-byte
/// mutation reaches, and this test asserts the stronger property: every
/// mutation is either refused by a nested decoder or accepted *and canonical*.
/// It does not require the backstop to catch something, because there is
/// nothing for it to catch; if a nested format regresses, the backstop fires
/// and the `non_canonical` count below says so.
///
/// **What this test may not claim.** Not every mutation is refused, so the
/// test does not assert that. A byte flipped inside
/// key material decodes to a *different but entirely canonical* session, and
/// the boundary cannot distinguish a different key from a wrong one -- that is
/// authentication's job, not canonicity's. The claim here is narrower
/// and is the one that matters: **some** mutation decodes and re-encodes
/// differently, and every such case is caught.
#[test]
fn a_non_canonical_spelling_is_refused() {
    let session = an_established_session();
    let clean = session.export().to_vec();

    let mut non_canonical = 0usize;
    let mut other_refusals = 0usize;
    let mut accepted = 0usize;

    for i in 0..clean.len() {
        let mut dirty = clean.clone();
        dirty[i] ^= 0xFF;
        match Session::import(&dirty) {
            Err(SessionDecodeError::NonCanonical) => non_canonical += 1,
            Err(_) => other_refusals += 1,
            Ok(restored) => {
                accepted += 1;
                // Anything accepted must be the encoding of what it decodes to.
                // This is the invariant the boundary now guarantees, checked
                // rather than assumed.
                assert_eq!(
                    restored.export().as_slice(),
                    dirty.as_slice(),
                    "an accepted byte string must re-encode to itself (offset {i})"
                );
            }
        }
    }

    assert_eq!(
        non_canonical, 0,
        "a nested decoder accepted a spelling it does not re-emit and only the \
         session-level backstop caught it: {non_canonical} non-canonical, \
         {other_refusals} other refusals, {accepted} accepted. Fix the nested \
         decoder; the backstop is not the place for canonicality to live"
    );
    assert!(other_refusals > 0, "no mutation was refused at all");

    println!(
        "canonicity: {non_canonical} refused as non-canonical, \
         {other_refusals} refused otherwise, {accepted} accepted and canonical"
    );
}
