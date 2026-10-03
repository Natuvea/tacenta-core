//! Nothing a stored session or a peer can supply makes the agreement's own
//! send enter `Failed`.
//!
//! `Session::encrypt` commits the agreement's next state when that state is
//! `Failed` (`self.braid = braid_next` in the `braid_next.failed()` branch).
//! No test can hold that commit: the branch is reached only if a send fails
//! inside the agreement, and the specification calls both failures defensive
//! (`mlkem-braid.md`, Failure). A send enters `Failed` in two places, the key
//! generation of the first transition and the first half of the encapsulation
//! of the seventh. Both call the key-encapsulation library (libcrux-ml-kem
//! 0.0.10), which fails there only on a buffer or input of the wrong length.
//! The key pair and the output buffers have lengths the build fixes. The one
//! input that comes from outside is the received header the encapsulation
//! reads, and it has exactly the right length in every state the library
//! builds or accepts: a completed header is decoded by a decoder sized for it,
//! and `Braid::invariant` requires that length of every state a stored session
//! carries.
//!
//! These tests hold the facts that argument rests on, through the public
//! interface, so that the commit stays unreachable on purpose:
//!
//! - a stored session whose received header has any length but the right one
//!   does not import;
//! - the 64 bytes of a received header, which the peer chooses, and the random
//!   source, which the caller chooses, do not make a send fail.
//!
//! If one of them starts to fail, a send may be able to enter `Failed` and the
//! commit in `Session::encrypt` needs a test of its own: `GAP-REGISTER.md`, row
//! `E2E-07-UNTESTED-CASES`.

use rand::SeedableRng;
use tacenta_core::sessions::{
    Identity, Session, SessionDecodeError, establish_initiator, establish_responder,
};

fn rng(seed: u64) -> rand::rngs::StdRng {
    rand::rngs::StdRng::seed_from_u64(seed)
}

/// A random source that returns one byte value forever. It is a valid
/// `CryptoRng` as far as the type system goes, and the worst one a caller
/// could hand in: every seed and every randomness the agreement draws is
/// constant.
struct Constant(u8);

impl rand::RngCore for Constant {
    fn next_u32(&mut self) -> u32 {
        u32::from_ne_bytes([self.0; 4])
    }
    fn next_u64(&mut self) -> u64 {
        u64::from_ne_bytes([self.0; 8])
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        dest.fill(self.0);
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl rand::CryptoRng for Constant {}

fn be32(bytes: &[u8], at: usize) -> usize {
    let mut word = [0u8; 4];
    word.copy_from_slice(&bytes[at..at + 4]);
    u32::from_be_bytes(word) as usize
}

/// Where the agreement sits in an exported session: the session is its
/// version byte, the length-prefixed Triple Ratchet and the length-prefixed
/// agreement (`session-persistence.md`, Session). Returns the offset of the
/// agreement's first byte and its length.
fn agreement_span(session: &[u8]) -> (usize, usize) {
    let at = 1 + 4 + be32(session, 1);
    (at + 4, be32(session, at))
}

/// The agreement's state tag, the second byte of its encoding.
const KEYS_UNSAMPLED: u8 = 0;
const HEADER_RECEIVED: u8 = 6;

fn agreement_tag(session: &Session) -> u8 {
    let bytes = session.export();
    let (start, _) = agreement_span(&bytes);
    bytes[start + 1]
}

/// An exported responder session whose agreement has received the initiator's
/// whole header and has not yet sent anything back, so that its next send is
/// the encapsulation. Returns the export and the offset of the header's
/// length prefix.
fn responder_holding_a_header() -> (Vec<u8>, usize) {
    let mut r = rng(41);
    let alice_id = Identity::generate(&mut r);
    let bob_id = Identity::generate(&mut r);
    let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);
    let bundle = bob_prekeys.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
    let initial = alice.encrypt(b"hello", &mut r).unwrap();
    let (mut bob, _) = establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();

    // The header is a few chunks long. Bounded, so a change to the chunking
    // fails here and not by looping.
    let mut sent = 0;
    while agreement_tag(&bob) != HEADER_RECEIVED && sent < 32 {
        let message = alice.encrypt(b"more", &mut r).unwrap();
        bob.decrypt(&message, &mut r).unwrap();
        sent += 1;
    }
    assert_eq!(
        agreement_tag(&bob),
        HEADER_RECEIVED,
        "the responder's agreement has received the header"
    );

    // Version, tag, epoch (8) and authenticator (64), then the header with its
    // four-byte length.
    let bytes = bob.export().to_vec();
    let (start, _) = agreement_span(&bytes);
    let header_at = start + 2 + 8 + 64;
    assert_eq!(be32(&bytes, header_at), 64, "the header is 64 bytes");
    (bytes, header_at)
}

/// A stored session whose received header is not 64 bytes is refused at the
/// door, so the encapsulation never sees one.
///
/// The control is the unaltered export, which imports. Each altered copy
/// carries a header of another length, with the header's own length prefix and
/// the agreement's length prefix rewritten to match, so the only thing wrong
/// with it is the length.
#[test]
fn a_stored_header_of_the_wrong_length_does_not_import() {
    let (bytes, header_at) = responder_holding_a_header();
    assert!(
        Session::import(&bytes).is_ok(),
        "the unaltered export imports"
    );
    let (start, length) = agreement_span(&bytes);

    for wrong in [0usize, 1, 32, 63, 65, 96, 4096] {
        let mut altered = Vec::new();
        altered.extend_from_slice(&bytes[..header_at]);
        altered.extend_from_slice(&(wrong as u32).to_be_bytes());
        altered.extend_from_slice(&vec![0x5A; wrong]);
        altered.extend_from_slice(&bytes[header_at + 4 + 64..]);
        let agreement_length = (length - 64 + wrong) as u32;
        altered[start - 4..start].copy_from_slice(&agreement_length.to_be_bytes());
        assert_eq!(
            Session::import(&altered).err(),
            Some(SessionDecodeError::Malformed),
            "a stored header of {wrong} bytes must not import"
        );
    }
}

/// The content of a received header does not make the send that reads it fail.
///
/// A peer chooses the 64 bytes, subject only to the authenticator on the
/// header, which the peer can compute. The copies below hold headers that are
/// not any key pair's: constant bytes and a counting pattern. Each imports
/// (the state is one the library accepts) and the next send, which runs the
/// encapsulation over the header, returns a message and leaves the agreement
/// running.
#[test]
fn the_content_of_a_received_header_does_not_make_a_send_fail() {
    let (bytes, header_at) = responder_holding_a_header();
    let content = header_at + 4;
    let counting: Vec<u8> = (0..64u8).collect();
    let patterns: [(&str, Vec<u8>); 4] = [
        ("zeros", vec![0x00; 64]),
        ("ones", vec![0xFF; 64]),
        ("a5", vec![0xA5; 64]),
        ("counting", counting),
    ];
    let mut r = rng(42);
    for (label, pattern) in patterns {
        let mut altered = bytes.clone();
        altered[content..content + 64].copy_from_slice(&pattern);
        let mut session = Session::import(&altered)
            .unwrap_or_else(|_| panic!("a header of {label} bytes imports"));
        assert!(
            session.encrypt(b"reply", &mut r).is_ok(),
            "the encapsulation over a header of {label} bytes must not fail"
        );
        assert!(
            !session.agreement_failed(),
            "a header of {label} bytes must not leave the agreement failed"
        );
    }
}

/// The random source does not make a send fail.
///
/// An initiator's first send is the key generation. A source that returns the
/// same byte forever is the worst case a caller can pass: the generation
/// completes, the session sends, and the agreement is not failed. The
/// responder's encapsulation draws from the same source and is covered by the
/// test above with a seeded one; here it is run under the constant source as
/// well.
#[test]
fn a_constant_random_source_does_not_make_a_send_fail() {
    for byte in [0x00u8, 0xFF, 0x01] {
        let mut r = rng(43);
        let alice_id = Identity::generate(&mut r);
        let bob_id = Identity::generate(&mut r);
        let bob_prekeys = bob_id.create_prekeys(2, &mut r);
        let bundle = bob_prekeys.publish();

        let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        assert_eq!(
            agreement_tag(&alice),
            KEYS_UNSAMPLED,
            "the first send is the key generation"
        );
        assert!(
            alice.encrypt(b"hello", &mut Constant(byte)).is_ok(),
            "key generation over a constant source ({byte:#04x}) must not fail"
        );
        assert!(!alice.agreement_failed());

        let (bytes, _) = responder_holding_a_header();
        let mut bob = Session::import(&bytes).unwrap();
        assert!(
            bob.encrypt(b"reply", &mut Constant(byte)).is_ok(),
            "the encapsulation over a constant source ({byte:#04x}) must not fail"
        );
        assert!(!bob.agreement_failed());
    }
}
