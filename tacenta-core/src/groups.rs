//! Public commitments for the bounded group fan-out validation profile.
//!
//! The product owns canonical roster and application-context encoding. These
//! helpers deliberately accept those bytes without parsing them, bind them to
//! separate fixed SHA-256 domains, and return their 32-byte commitments.

use sha2::{Digest, Sha256};

/// Canonical public inventory preimages for the initial hosted-device profile.
/// This parses no product account type and does not authorize group membership.
pub mod inventory;

/// Domain separation for a canonical product roster preimage.
pub const GROUP_ROSTER_COMMITMENT_LABEL: &[u8] = b"Tacenta:group:roster-commitment:v1\xff";
/// Domain separation for a canonical authenticated application context.
pub const GROUP_PAYLOAD_COMMITMENT_LABEL: &[u8] = b"Tacenta:group:payload-commitment:v1\xff";

/// The fixed length of either version-one group commitment.
pub const GROUP_COMMITMENT_LEN: usize = 32;

/// Computes the commitment of an already canonical bounded group roster
/// preimage. Parsing, canonicality, and membership validation remain product
/// responsibilities; callers must not use this helper as validation.
pub fn roster_commitment(preimage: &[u8]) -> [u8; GROUP_COMMITMENT_LEN] {
    commitment(GROUP_ROSTER_COMMITMENT_LABEL, preimage)
}

/// Computes the commitment of an already canonical bounded group application
/// context. The context must reside inside pairwise-authenticated plaintext;
/// this helper does not authenticate a peer or alter pairwise associated data.
pub fn payload_commitment(context: &[u8]) -> [u8; GROUP_COMMITMENT_LEN] {
    commitment(GROUP_PAYLOAD_COMMITMENT_LABEL, context)
}

fn commitment(label: &[u8], value: &[u8]) -> [u8; GROUP_COMMITMENT_LEN] {
    let mut digest = Sha256::new();
    digest.update(label);
    digest.update(value);
    digest.finalize().into()
}
