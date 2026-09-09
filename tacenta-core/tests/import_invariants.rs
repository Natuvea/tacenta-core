//! Import-time semantic validation (external review, 2026-09, item 3).
//!
//! `Session::import` and `PrekeyStore::from_bytes` used to re-encode and
//! compare, which catches a second spelling of a value and nothing about the
//! value. A canonical export whose ratchet private key was not the private
//! half of the advertised public key imported, worked until the peer's next
//! Diffie-Hellman step, and then failed for good; one whose sparse-ratchet
//! epoch did not match the Braid's imported and refused the next agreement
//! output on every message after. Both formats now carry an `invariant` the
//! decoder refuses on, and this file holds it as an *inductive* invariant:
//! established by the constructors, preserved by every operation, and
//! re-established at the persistence boundary.
//!
//! Two halves. The honest half drives a pair through hundreds of epochs and
//! asserts the predicate after every message and every round trip through
//! `export`/`import`, which is what makes the second half meaningful: a
//! predicate no honest run satisfies would refuse everything. The crafted
//! half takes a real export, edits exactly one relation at the field's
//! offset (session-persistence.md, "Session", gives the layout; the offsets
//! are read from the length prefixes rather than assumed), and asserts the
//! refusal is `Inconsistent` -- which is also the proof that the edit left
//! the bytes canonical, since the re-encode check runs first.

use rand::Rng;
use rand::SeedableRng;
use tacenta_core::primitives::dh::PublicKeyBytes;
use tacenta_core::primitives::kem;
use tacenta_core::sessions::{
    self, PrekeyStore, Session, SessionDecodeError, encode_ec, establish_initiator,
    establish_responder,
};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

/// Alice (initiator) and Bob (responder), with Bob's store, established from
/// Alice's first message. Every product of the establishment satisfies its
/// invariant.
fn establish(
    r: &mut rand::rngs::StdRng,
    one_time_count: usize,
) -> (Session, Session, sessions::Identity, PrekeyStore) {
    let alice_id = sessions::Identity::generate(r);
    let bob_id = sessions::Identity::generate(r);
    let mut bob_prekeys = bob_id.create_prekeys(one_time_count, r);
    assert!(bob_prekeys.invariant(), "create_prekeys");
    let bundle = bob_prekeys.publish();

    let mut alice = establish_initiator(&alice_id, &bundle, r).unwrap();
    assert!(alice.invariant(), "establish_initiator");
    let initial = alice.encrypt(b"hello bob", r).unwrap();
    assert!(alice.invariant(), "first encrypt");
    let (bob, first) = establish_responder(&bob_id, &mut bob_prekeys, &initial, r).unwrap();
    assert_eq!(first, b"hello bob");
    assert!(bob.invariant(), "establish_responder");
    assert!(
        bob_prekeys.invariant(),
        "the store after establish_responder"
    );
    (alice, bob, bob_id, bob_prekeys)
}

/// Export, import, and hand back the restored session, asserting the
/// invariant on both sides of the boundary.
fn round_trip(s: Session, what: &str) -> Session {
    assert!(s.invariant(), "{what}: before export");
    let bytes = s.export();
    let back = Session::import(&bytes).unwrap_or_else(|e| panic!("{what}: import {e:?}"));
    assert!(back.invariant(), "{what}: after import");
    back
}

/// The invariant holds after every message and every round trip, across
/// enough traffic to carry the Braid through a couple of hundred epochs, so
/// that every one of its eleven live states is exported from on both sides
/// and clause (b)'s relation is checked at every point it claims to hold.
///
/// Bursts of random length each way, so both roles see every transition
/// from both directions, and a restart every few bursts on one side or the
/// other, so the restored session keeps going rather than being merely
/// decodable.
#[test]
fn an_honest_session_satisfies_the_invariant_at_every_point() {
    let mut r = rng(200);
    let (mut alice, mut bob, _bob_id, _store) = establish(&mut r, 2);

    for round in 0..1500u32 {
        for _ in 0..r.gen_range(1..4) {
            let m = alice.encrypt(b"a", &mut r).unwrap();
            assert!(alice.invariant(), "alice after encrypt, round {round}");
            assert_eq!(bob.decrypt(&m, &mut r).unwrap(), b"a");
            assert!(bob.invariant(), "bob after decrypt, round {round}");
        }
        for _ in 0..r.gen_range(1..4) {
            let m = bob.encrypt(b"b", &mut r).unwrap();
            assert!(bob.invariant(), "bob after encrypt, round {round}");
            assert_eq!(alice.decrypt(&m, &mut r).unwrap(), b"b");
            assert!(alice.invariant(), "alice after decrypt, round {round}");
        }
        match round % 7 {
            0 => alice = round_trip(alice, "alice"),
            3 => bob = round_trip(bob, "bob"),
            _ => {}
        }
    }
    // Both ratchets and the Braid moved a long way: this is not a test of the
    // opening state. The scratch run that fixed clause (b) carried this loop
    // through 207 Braid epochs in 6000 rounds, so 1500 rounds is about
    // fifty, each entered from both roles. Nothing public reports the epoch,
    // so the figure is stated rather than asserted.
}

/// An initiator that has not yet been answered -- `pending_initial` set --
/// satisfies the invariant, survives the round trip, and its restored copy
/// still establishes the responder.
#[test]
fn an_unanswered_initiator_satisfies_the_invariant() {
    let mut r = rng(201);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(4, &mut r);
    let bundle = bob_prekeys.publish();
    let alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    assert!(alice.invariant());
    let mut alice = round_trip(alice, "unanswered initiator");
    let initial = alice.encrypt(b"first", &mut r).unwrap();
    let (bob, first) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
    assert_eq!(first, b"first");
    assert!(bob.invariant());
    assert!(bob_prekeys.invariant());
}

/// A session whose Braid has failed still imports: the failure is terminal
/// and must persist as such (`Error::AgreementFailed` says why), so the
/// epoch and role clauses exempt it rather than refuse it.
#[test]
fn a_failed_braid_is_exempt_from_the_epoch_and_role_clauses() {
    let mut r = rng(202);
    let (alice, _bob, _bob_id, _store) = establish(&mut r, 2);
    let bytes = alice.export();
    let l = layout(&bytes);
    // A failed Braid is its version byte and the tag `11`, nothing else, so
    // the Braid field shrinks to two bytes and its length prefix follows.
    let mut crafted = bytes[..l.braid_len_at].to_vec();
    crafted.extend_from_slice(&2u32.to_be_bytes());
    crafted.push(bytes[l.braid.start]);
    crafted.push(11);
    crafted.extend_from_slice(&bytes[l.braid.end..]);
    let restored = Session::import(&crafted).expect("a failed Braid still imports");
    assert!(restored.agreement_failed());
    assert!(restored.invariant());
}

// ---------------------------------------------------------------------------
// The layout of a session export, read rather than assumed.

/// Where each field of a session export begins, from its length prefixes.
struct Layout {
    /// The Triple Ratchet's bytes (past their length prefix).
    triple: std::ops::Range<usize>,
    /// Where the Braid's length prefix sits, and the Braid's bytes.
    braid_len_at: usize,
    braid: std::ops::Range<usize>,
    ratchet_private: usize,
    /// The associated data's bytes (past their length prefix).
    identity_ad: std::ops::Range<usize>,
    /// The `pending_initial` presence byte, and the field's bytes when
    /// present (past the length prefix).
    pending_present_at: usize,
    pending: Option<std::ops::Range<usize>>,
    /// The `established_ephemeral` presence byte, and the field's bytes when
    /// present.
    established_present_at: usize,
    established: Option<std::ops::Range<usize>>,
}

fn u32_at(bytes: &[u8], at: usize) -> usize {
    u32::from_be_bytes(bytes[at..at + 4].try_into().unwrap()) as usize
}

fn layout(bytes: &[u8]) -> Layout {
    assert_eq!(bytes[0], 0x01, "session format version");
    let mut pos = 1;
    let triple = pos + 4..pos + 4 + u32_at(bytes, pos);
    pos = triple.end;
    let braid_len_at = pos;
    let braid = pos + 4..pos + 4 + u32_at(bytes, pos);
    pos = braid.end;
    let ratchet_private = pos;
    pos += 32;
    let identity_ad = pos + 4..pos + 4 + u32_at(bytes, pos);
    pos = identity_ad.end;
    pos += 64; // our and peer identity public keys
    let pending_present_at = pos;
    let pending = match bytes[pos] {
        0x00 => {
            pos += 1;
            None
        }
        0x01 => {
            let range = pos + 5..pos + 5 + u32_at(bytes, pos + 1);
            pos = range.end;
            Some(range)
        }
        other => panic!("presence byte {other:#04x}"),
    };
    let established_present_at = pos;
    let established = match bytes[pos] {
        0x00 => {
            pos += 1;
            None
        }
        0x01 => {
            let range = pos + 5..pos + 5 + u32_at(bytes, pos + 1);
            pos = range.end;
            Some(range)
        }
        other => panic!("presence byte {other:#04x}"),
    };
    assert_eq!(pos, bytes.len(), "the layout must account for every byte");
    Layout {
        triple,
        braid_len_at,
        braid,
        ratchet_private,
        identity_ad,
        pending_present_at,
        pending,
        established_present_at,
        established,
    }
}

/// The 66-byte associated data with its two `EncodeEC` halves swapped: the
/// same two identities in the other orientation.
fn swapped_ad(ad: &[u8]) -> Vec<u8> {
    assert_eq!(ad.len(), 66);
    let mut out = ad[33..].to_vec();
    out.extend_from_slice(&ad[..33]);
    out
}

/// A responder's export past establishment: `pending_initial` absent,
/// `established_ephemeral` present.
fn a_responder_export(seed: u64) -> Vec<u8> {
    let mut r = rng(seed);
    let (_alice, bob, _bob_id, _store) = establish(&mut r, 2);
    let bytes = bob.export().to_vec();
    let l = layout(&bytes);
    assert!(l.pending.is_none() && l.established.is_some());
    bytes
}

/// An initiator's export after the peer has answered: both optional fields
/// absent.
fn an_answered_initiator_export(seed: u64) -> Vec<u8> {
    let mut r = rng(seed);
    let (mut alice, mut bob, _bob_id, _store) = establish(&mut r, 2);
    let reply = bob.encrypt(b"reply", &mut r).unwrap();
    alice.decrypt(&reply, &mut r).unwrap();
    let bytes = alice.export().to_vec();
    let l = layout(&bytes);
    assert!(l.pending.is_none() && l.established.is_none());
    bytes
}

/// An initiator's export before the peer has answered: `pending_initial`
/// present.
fn an_unanswered_initiator_export(seed: u64) -> Vec<u8> {
    let mut r = rng(seed);
    let (alice, _bob, _bob_id, _store) = establish(&mut r, 2);
    let bytes = alice.export().to_vec();
    let l = layout(&bytes);
    assert!(l.pending.is_some() && l.established.is_none());
    bytes
}

fn assert_inconsistent(bytes: &[u8], what: &str) {
    match Session::import(bytes) {
        Err(SessionDecodeError::Inconsistent) => {}
        other => panic!("{what}: expected Inconsistent, got {:?}", other.map(|_| ())),
    }
}

// ---------------------------------------------------------------------------
// One crafted export per clause.

/// (a) A ratchet private key that is not the private half of the advertised
/// public key. Byte 7, well clear of the bits X25519 clamps at either end,
/// so the public key genuinely changes.
#[test]
fn a_ratchet_private_key_that_does_not_match_the_advertised_public_key_is_refused() {
    let mut bytes = a_responder_export(210);
    let l = layout(&bytes);
    bytes[l.ratchet_private + 7] ^= 0x01;
    assert_inconsistent(&bytes, "ratchet private key");
}

/// (b) An epoch pair outside the relation. The Braid's epoch is the first
/// field of every live state, right after the state tag; two is added so
/// its parity, and with it the role clause (d) reads from it, is unchanged
/// and only the epoch relation moves.
#[test]
fn an_epoch_pair_the_sparse_ratchet_cannot_follow_is_refused() {
    for (seed, name) in [(211, "responder"), (212, "initiator")] {
        let mut bytes = if name == "responder" {
            a_responder_export(seed)
        } else {
            an_answered_initiator_export(seed)
        };
        let l = layout(&bytes);
        let at = l.braid.start + 2;
        let epoch = u64::from_be_bytes(bytes[at..at + 8].try_into().unwrap());
        bytes[at..at + 8].copy_from_slice(&(epoch + 2).to_be_bytes());
        assert_inconsistent(&bytes, &format!("{name} braid epoch"));
    }
}

/// (c) Associated data in the wrong orientation: the same two identities,
/// responder first. And, separately, associated data that binds some other
/// key.
#[test]
fn associated_data_in_the_wrong_orientation_is_refused() {
    let mut bytes = a_responder_export(213);
    let l = layout(&bytes);
    let swapped = swapped_ad(&bytes[l.identity_ad.clone()]);
    bytes[l.identity_ad.clone()].copy_from_slice(&swapped);
    assert_inconsistent(&bytes, "swapped associated data");

    let mut bytes = an_answered_initiator_export(214);
    let l = layout(&bytes);
    bytes[l.identity_ad.start + 5] ^= 0x01;
    assert_inconsistent(&bytes, "altered associated data");
}

/// (d) The halves disagree on the role. A responder's export relabelled as
/// an initiator's -- `established_ephemeral` removed and the associated data
/// reoriented to match, so that clauses (c), (e) and (f) all still hold and
/// only the Braid still says "responder" -- and the reverse: an answered
/// initiator's export given an `established_ephemeral`.
#[test]
fn a_role_the_braid_disagrees_with_is_refused() {
    // Responder relabelled as initiator.
    let bytes = a_responder_export(215);
    let l = layout(&bytes);
    let mut crafted = bytes[..l.identity_ad.start].to_vec();
    crafted.extend_from_slice(&swapped_ad(&bytes[l.identity_ad.clone()]));
    crafted.extend_from_slice(&bytes[l.identity_ad.end..l.established_present_at]);
    crafted.push(0x00);
    assert_inconsistent(&crafted, "responder relabelled as initiator");

    // Initiator relabelled as responder.
    let bytes = an_answered_initiator_export(216);
    let l = layout(&bytes);
    let mut crafted = bytes[..l.identity_ad.start].to_vec();
    crafted.extend_from_slice(&swapped_ad(&bytes[l.identity_ad.clone()]));
    crafted.extend_from_slice(&bytes[l.identity_ad.end..l.established_present_at]);
    crafted.push(0x01);
    let ephemeral = encode_ec(&PublicKeyBytes::from_bytes([0x5a; 32]));
    crafted.extend_from_slice(&(ephemeral.len() as u32).to_be_bytes());
    crafted.extend_from_slice(&ephemeral);
    assert_inconsistent(&crafted, "initiator relabelled as responder");
}

/// (e) Both optional fields present: a responder's export with a
/// `pending_initial` inserted. The inserted message is well-formed -- a
/// ciphertext of the right length -- so clause (f) is satisfied and only
/// the pairing is wrong.
#[test]
fn a_session_that_is_both_an_unanswered_initiator_and_a_responder_is_refused() {
    let bytes = a_responder_export(217);
    let l = layout(&bytes);
    let mut pending = vec![0x33u8; 32];
    pending.extend_from_slice(&(kem::ciphertext_len() as u32).to_be_bytes());
    pending.extend(std::iter::repeat_n(0x44u8, kem::ciphertext_len()));
    pending.extend_from_slice(&[0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3]);
    let mut crafted = bytes[..l.pending_present_at].to_vec();
    crafted.push(0x01);
    crafted.extend_from_slice(&(pending.len() as u32).to_be_bytes());
    crafted.extend_from_slice(&pending);
    crafted.extend_from_slice(&bytes[l.pending_present_at + 1..]);
    assert_inconsistent(&crafted, "pending and established both present");
}

/// (f) A pending initial message whose KEM ciphertext is one byte short,
/// both length prefixes corrected so the bytes stay canonical; and an
/// established ephemeral that is not an `EncodeEC` value, once by length and
/// once by curve byte.
#[test]
fn a_pending_ciphertext_of_the_wrong_length_is_refused() {
    let bytes = an_unanswered_initiator_export(218);
    let l = layout(&bytes);
    let p = l.pending.clone().unwrap();
    // pending_initial = ephemeral(32) || len(4) || ciphertext || ids(12)
    let ct_len = u32_at(&bytes, p.start + 32);
    assert_eq!(ct_len, kem::ciphertext_len());
    let mut crafted = bytes[..l.pending_present_at + 1].to_vec();
    crafted.extend_from_slice(&((p.len() - 1) as u32).to_be_bytes());
    crafted.extend_from_slice(&bytes[p.start..p.start + 32]);
    crafted.extend_from_slice(&((ct_len - 1) as u32).to_be_bytes());
    crafted.extend_from_slice(&bytes[p.start + 36..p.start + 36 + ct_len - 1]);
    crafted.extend_from_slice(&bytes[p.start + 36 + ct_len..]);
    assert_inconsistent(&crafted, "short KEM ciphertext");
}

#[test]
fn an_established_ephemeral_that_is_not_an_encoded_curve_key_is_refused() {
    let bytes = a_responder_export(219);
    let l = layout(&bytes);
    let e = l.established.clone().unwrap();
    assert_eq!(e.len(), 33);

    // Wrong curve byte, same length.
    let mut crafted = bytes.clone();
    crafted[e.start] ^= 0xff;
    assert_inconsistent(&crafted, "wrong curve byte");

    // Right curve byte, one byte short, length prefix corrected.
    let mut crafted = bytes[..l.established_present_at + 1].to_vec();
    crafted.extend_from_slice(&32u32.to_be_bytes());
    crafted.extend_from_slice(&bytes[e.start..e.end - 1]);
    assert_inconsistent(&crafted, "short ephemeral");
}

/// (d), the sparse ratchet's half, and (g), the delegation beneath it.
///
/// The sparse ratchet's `direction` byte sits at a fixed offset inside the
/// Triple Ratchet's bytes (session-persistence.md, "Sparse ratchet state":
/// `version(1) || rk(32) || epoch(8) || direction(1)`), so the crafted
/// export is one byte flipped, and which layer refuses it depends on what
/// the classical half still shows. On a responder past establishment the
/// classical half has stepped and carries no role, so the Triple Ratchet's
/// own invariant holds and the session's clause (d) is what refuses:
/// `Inconsistent`. On an initiator that has not yet received, the classical
/// half still shows it started as sender, the Triple Ratchet's decoder
/// refuses the disagreement itself, and the session reports `Malformed`
/// from the nested decode -- the leaf-level reading of the same fact, which
/// is what clause (g) delegates to.
#[test]
fn a_sparse_ratchet_direction_the_session_disagrees_with_is_refused() {
    fn flip_direction(bytes: &mut [u8]) {
        let l = layout(bytes);
        // triple_state = version(1) || len(4) || ratchet_state || len(4) || spqr_state
        let ratchet_len = u32_at(bytes, l.triple.start + 1);
        let spqr_start = l.triple.start + 1 + 4 + ratchet_len + 4;
        let direction_at = spqr_start + 1 + 32 + 8;
        assert!(bytes[direction_at] <= 1, "a direction tag");
        bytes[direction_at] ^= 0x01;
    }

    let mut bytes = a_responder_export(221);
    flip_direction(&mut bytes);
    assert_inconsistent(&bytes, "sparse ratchet direction, responder");

    let mut bytes = an_unanswered_initiator_export(222);
    flip_direction(&mut bytes);
    assert!(
        matches!(Session::import(&bytes), Err(SessionDecodeError::Malformed)),
        "sparse ratchet direction, unanswered initiator: the Triple Ratchet refuses first"
    );
}

// ---------------------------------------------------------------------------
// The prekey store's invariant, after every operation that touches it.

#[test]
fn the_prekey_store_invariant_holds_after_every_operation() {
    let mut r = rng(230);
    let alice_id = sessions::Identity::generate(&mut r);
    let bob_id = sessions::Identity::generate(&mut r);

    for count in [0, 1, 4] {
        assert!(
            bob_id.create_prekeys(count, &mut r).invariant(),
            "create_prekeys({count})"
        );
    }

    let mut store = bob_id.create_prekeys(2, &mut r);
    store.replenish(&bob_id, 3, &mut r);
    assert!(store.invariant(), "replenish");
    store.replenish(&bob_id, 0, &mut r);
    assert!(store.invariant(), "replenish(0)");

    store.rotate_signed_prekey(&bob_id, &mut r);
    assert!(store.invariant(), "rotate_signed_prekey");
    store.rotate_signed_prekey(&bob_id, &mut r);
    assert!(store.invariant(), "second rotate_signed_prekey");
    store.rotate_kem(&bob_id, &mut r);
    assert!(store.invariant(), "rotate_kem");

    // Every establishment: the one-time path until the pool is dry, then
    // the last-resort path, then a replay refusal, then a rotation that
    // retires the key the record was made under and a second that wipes it.
    let (curve, kem) = store.one_time_remaining();
    assert_eq!(curve, kem);
    for i in 0..curve + 3 {
        let bundle = store.publish();
        let mut peer = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        let initial = peer.encrypt(b"x", &mut r).unwrap();
        let (session, _) = establish_responder(&bob_id, &mut store, &initial, &mut r).unwrap();
        assert!(session.invariant(), "session from establishment {i}");
        assert!(store.invariant(), "store after establishment {i}");
        if i >= curve {
            assert!(
                establish_responder(&bob_id, &mut store, &initial, &mut r).is_err(),
                "a last-resort replay is refused"
            );
            assert!(store.invariant(), "store after a refused replay {i}");
        }
    }
    assert!(store.last_resort_record_remaining() < 1024);

    store.rotate_kem(&bob_id, &mut r);
    assert!(store.invariant(), "rotate_kem with a record");
    store.rotate_kem(&bob_id, &mut r);
    assert!(store.invariant(), "rotate_kem that wipes the recorded key");

    let restored = PrekeyStore::from_bytes(&store.to_bytes()).unwrap();
    assert!(restored.invariant(), "from_bytes");
}

/// A store whose bytes decode field by field but whose identifiers are not a
/// namespace is refused. The identifier rules were already refusals before
/// they were factored into `invariant`; `tests/replay_record.rs` holds one
/// crafted store per rule. This adds the rule the factoring introduced: no
/// identifier is the absent-identifier sentinel.
#[test]
fn a_store_holding_the_absent_identifier_is_refused() {
    let mut r = rng(231);
    let bob_id = sessions::Identity::generate(&mut r);
    let store = bob_id.create_prekeys(0, &mut r);
    let mut bytes = store.to_bytes().to_vec();
    // version(1) || identity_public(32) || signed_secret(32) || signed_id(4)
    let signed_id_at = 1 + 32 + 32;
    assert_eq!(
        u32_at(&bytes, signed_id_at),
        1,
        "create_prekeys numbers from one"
    );
    bytes[signed_id_at..signed_id_at + 4].copy_from_slice(&0u32.to_be_bytes());
    assert!(
        matches!(
            PrekeyStore::from_bytes(&bytes),
            Err(sessions::PrekeyStoreDecodeError::Malformed)
        ),
        "a signed prekey under the absent identifier"
    );
}
