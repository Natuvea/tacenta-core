//! The ratchet's message key drives the AEAD.
//!
//! This test lives here rather than in the `tacenta-ratchet` leaf crate because
//! the AEAD is outside the verified zone: the leaf carries only the ratchet's
//! key schedule and the derivation it calls, so the T1 translation covers
//! exactly that. Composing a message key with the AEAD is a tacenta-core
//! concern, so it is tested at that layer.

use tacenta_core::primitives::aead;
use tacenta_core::ratchet::{
    Key, LabelSet, init_receiver, init_sender, message_keys, receive, send,
};

const SK: Key = [0x01; 32];
const A_PUB: Key = [0x0a; 32];
const B_PUB: Key = [0x0b; 32];
const B2_PUB: Key = [0x2b; 32];
const DH_AB: Key = [0xab; 32];
const DH_B2A: Key = [0xba; 32];

#[test]
fn message_key_drives_the_aead_round_trip() {
    // The ratchet's message key expands into AEAD material that encrypts and
    // decrypts a message, with the header bound as associated data.
    let mut sa = init_sender(&SK, A_PUB, B_PUB, &DH_AB, LabelSet::Tacenta);
    let (h0, mk_send) = send(&mut sa).unwrap();
    let mut sb = init_receiver(&SK, B_PUB, LabelSet::Tacenta);
    let mk_recv = receive(&mut sb, &h0, &DH_AB, &DH_B2A, B2_PUB).unwrap();

    let ad = h0.dh; // stands in for the serialized header
    let (enc_s, mac_s, iv_s) = message_keys(&mk_send, LabelSet::Tacenta);
    let ct = aead::encrypt(&enc_s, &mac_s, &iv_s, b"hello ratchet", &ad);
    let (enc_r, mac_r, iv_r) = message_keys(&mk_recv, LabelSet::Tacenta);
    let pt = aead::decrypt(&enc_r, &mac_r, &iv_r, &ct, &ad).unwrap();
    assert_eq!(pt, b"hello ratchet");
}
