//! sessions: PQXDH session establishment.
//!
//! This module follows tacenta-spec/protocol/session-establishment.md and the
//! model in tacenta-model (`Model.SessionEstablishment`).
//!
//! The boundary is the same as the ratchet's: the Diffie-Hellman agreements and
//! the post-quantum encapsulation are trusted primitives, so their outputs enter
//! here as bytes. What this module computes is the derivation that combines
//! them, which is PQXDH's own contribution. The encapsulated secret stays an
//! argument rather than something this module produces, so the derivation is
//! checkable against the model without a KEM in the loop; callers obtain it from
//! `primitives::kem` (ML-KEM-1024). The full handshake is exercised end to end
//! in this module's tests and in tests/handshake_to_ratchet.rs.

use crate::primitives::{dh, xeddsa};
use zeroize::Zeroizing;

mod lifecycle;
pub use lifecycle::{
    Error as LifecycleError, Identity, PrekeyStore, PrekeyStoreDecodeError, PublicState,
    PublishedBundle, Session, SessionDecodeError, establish_initiator, establish_initiator_for,
    establish_responder,
};

/// The derivation itself lives in the `tacenta-session` leaf crate, which is
/// what T1 and T3 translate. Re-exported here so callers and the existing tests
/// keep one import path, and so nothing in this module can drift from the
/// version the proofs are about.
pub use tacenta_session::{
    ENCODE_EC_CURVE25519, ENCODE_EC_LEN, ENCODE_KEM_ML_KEM_1024, Key, associated_data,
    associated_data_with_kem, km, shared_secret,
};

/// `EncodeEC`: the curve byte followed by the public key.
///
/// A thin wrapper over the leaf crate's, which works in plain bytes so the
/// translated crate does not depend on the curve type.
pub fn encode_ec(pk: &dh::PublicKeyBytes) -> Vec<u8> {
    tacenta_session::encode_ec(pk.as_bytes())
}

/// `DecodeEC`: read a curve public key back from its `EncodeEC` form, or `None`
/// if the bytes are not one.
pub fn decode_ec(bytes: &[u8]) -> Option<dh::PublicKeyBytes> {
    // `map` here rather than the leaf crate's spelled-out match: this module is
    // not translated, so the closure costs nothing.
    tacenta_session::decode_ec(bytes).map(dh::PublicKeyBytes::from_bytes)
}

/// `EncodeKEM`: the KEM byte followed by the public key.
///
/// Public, like the curve pair above, because a caller composing a bundle has
/// to put components on the wire in the same encoding a
/// peer reads them in, and the published specifications leave composing a
/// bundle to the application rather than to the protocol.
pub fn encode_kem(pk: &[u8]) -> Vec<u8> {
    tacenta_session::encode_kem(pk)
}

/// `DecodeKEM`: read a KEM public key back from its `EncodeKEM` form, or `None`
/// if the bytes are not one.
pub fn decode_kem(bytes: &[u8]) -> Option<Vec<u8>> {
    match bytes.split_first() {
        Some((&tag, rest))
            if tag == tacenta_session::ENCODE_KEM_ML_KEM_1024 && !rest.is_empty() =>
        {
            Some(rest.to_vec())
        }
        _ => None,
    }
}

/// Verify a signature made by [`Identity::sign_message`] under a published
/// identity key.
///
/// The verifying side of device authentication, and the one place a deployment's
/// two halves must agree with each other rather than merely behave alike: a
/// client signing under one implementation and a server verifying under another
/// rejects every connection.
pub fn verify_under_identity(
    identity: &dh::PublicKeyBytes,
    message: &[u8],
    signature: &[u8; 64],
) -> bool {
    xeddsa::verify(identity, &application_signing_input(message), signature).is_ok()
}

/// The domain-separation prefix for signatures over caller-supplied messages.
///
/// **Why one side is tagged and the other is not.** `Identity` signs two very
/// different things with one key (ADR-0002): prekeys during the handshake, and
/// whatever a caller passes to `sign_message`. Without a separation they
/// would be the same operation over the same input space, so a caller who
/// could choose the "message" could obtain a signature in the shape of a
/// prekey signature, and a prekey signature could answer a challenge: a
/// cross-protocol signature oracle.
///
/// The obvious fix -- tag both purposes -- is unavailable, and the reason is
/// worth stating rather than discovering. The signed-prekey signature input is
/// part of the external interoperability profile and therefore left unchanged.
/// Bundle-layer interoperability is the one interoperability claim made
/// (README, "What is and is not claimed"), so prefixing what a prekey
/// signature covers would break it.
///
/// Tagging one side is enough, and it closes both directions. A signature made
/// here can never verify as a prekey signature, because a prekey verifier does
/// not prepend this prefix and the byte strings therefore differ. A prekey
/// signature can never answer a challenge, because a challenge verifier does
/// prepend it. The asymmetry buys the separation without touching the wire.
///
/// The `0xff` terminator cannot occur inside the label, so no message can
/// extend the label into a different one.
const APPLICATION_SIGNING_LABEL: &[u8] = b"tacenta:application-signature:v1\xff";

pub(crate) fn application_signing_input(message: &[u8]) -> Vec<u8> {
    let mut input = Vec::with_capacity(APPLICATION_SIGNING_LABEL.len() + message.len());
    input.extend_from_slice(APPLICATION_SIGNING_LABEL);
    input.extend_from_slice(message);
    input
}

/// A prekey bundle as fetched from the server. The KEM prekey is carried as
/// opaque bytes: which KEM key it is (a one-time key or the last-resort key)
/// does not change the derivation, and this type stays agnostic to the KEM's
/// own encoding. The KEM is wired -- `establish_initiator` encapsulates against
/// this prekey and folds the secret into the handshake -- so the bytes are what
/// `primitives::kem` produced, read back only by that module.
pub struct PreKeyBundle {
    pub identity_key: dh::PublicKeyBytes,
    pub signed_prekey: dh::PublicKeyBytes,
    pub signed_prekey_signature: [u8; 64],
    pub kem_prekey: Vec<u8>,
    pub kem_prekey_signature: [u8; 64],
    pub one_time_prekey: Option<dh::PublicKeyBytes>,
}

/// Failures establishing a session.
///
/// `#[non_exhaustive]`: pre-1.0, and the agreement checks can still gain
/// refusals, so a consumer must carry a wildcard arm (CR-27).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum SessionError {
    /// The signature over the signed curve prekey did not verify.
    BadSignedPrekeySignature,
    /// The signature over the KEM prekey did not verify.
    BadKemPrekeySignature,
    /// A Diffie-Hellman agreement was not contributory: the peer sent a
    /// low-order public key, which forces the shared secret to zero whatever
    /// our private key is. Rejected rather than used (`dh::PrivateKey::agree`).
    NonContributoryAgreement,
}

/// Verify both prekey signatures under the bundle's identity key. Alice must do
/// this before using a bundle: without it a malicious server could serve forged
/// prekeys and later compromise the identity key to recover the secret, which
/// would defeat forward secrecy.
pub fn verify_bundle(bundle: &PreKeyBundle) -> Result<(), SessionError> {
    xeddsa::verify(
        &bundle.identity_key,
        &encode_ec(&bundle.signed_prekey),
        &bundle.signed_prekey_signature,
    )
    .map_err(|_| SessionError::BadSignedPrekeySignature)?;
    xeddsa::verify(
        &bundle.identity_key,
        &encode_kem(&bundle.kem_prekey),
        &bundle.kem_prekey_signature,
    )
    .map_err(|_| SessionError::BadKemPrekeySignature)?;
    Ok(())
}

/// The initiator's side: verify the bundle, then compute the Diffie-Hellman
/// outputs and combine them with the encapsulated secret. `encapsulated` is the
/// secret the caller obtained from the KEM against the bundle's KEM prekey.
pub fn initiator_shared_secret(
    identity_private: &dh::PrivateKey,
    ephemeral_private: &dh::PrivateKey,
    bundle: &PreKeyBundle,
    encapsulated: &Key,
) -> Result<Key, SessionError> {
    verify_bundle(bundle)?;
    // Wiped on the way out. The specifications require the initiator to delete
    // the Diffie-Hellman outputs once the shared secret is derived, so they are
    // held in memory that erases rather than in plain arrays that go out of
    // scope untouched (key-deletion.md).
    // Any of these may refuse: the bundle's keys came from a directory we do
    // not trust, so a low-order prekey is a thing a hostile server can serve.
    let nc = SessionError::NonContributoryAgreement;
    let dh1 = Zeroizing::new(identity_private.agree(&bundle.signed_prekey).ok_or(nc)?);
    let dh2 = Zeroizing::new(ephemeral_private.agree(&bundle.identity_key).ok_or(nc)?);
    let dh3 = Zeroizing::new(ephemeral_private.agree(&bundle.signed_prekey).ok_or(nc)?);
    let dh4 = match bundle.one_time_prekey.as_ref() {
        Some(opk) => Some(Zeroizing::new(ephemeral_private.agree(opk).ok_or(nc)?)),
        None => None,
    };
    Ok(shared_secret(
        &dh1,
        &dh2,
        &dh3,
        dh4.as_deref(),
        encapsulated,
    ))
}

/// The responder's side: the same four agreements, computed from the other
/// direction's private keys, plus the secret decapsulated from the ciphertext.
/// Pass the one-time prekey private key exactly when the initiator used it.
pub fn responder_shared_secret(
    identity_private: &dh::PrivateKey,
    signed_prekey_private: &dh::PrivateKey,
    one_time_prekey_private: Option<&dh::PrivateKey>,
    initiator_identity: &dh::PublicKeyBytes,
    initiator_ephemeral: &dh::PublicKeyBytes,
    encapsulated: &Key,
) -> Result<Key, SessionError> {
    // Wiped on the way out, for the same reason as the initiator's above.
    //
    // Fallible for the same reason too, and the responder's case is the one
    // that matters more: these keys arrive in an *unauthenticated* initial
    // message, so anyone who can send us bytes chooses them.
    let nc = SessionError::NonContributoryAgreement;
    let dh1 = Zeroizing::new(signed_prekey_private.agree(initiator_identity).ok_or(nc)?);
    let dh2 = Zeroizing::new(identity_private.agree(initiator_ephemeral).ok_or(nc)?);
    let dh3 = Zeroizing::new(signed_prekey_private.agree(initiator_ephemeral).ok_or(nc)?);
    let dh4 = match one_time_prekey_private {
        Some(opk) => Some(Zeroizing::new(opk.agree(initiator_ephemeral).ok_or(nc)?)),
        None => None,
    };
    Ok(shared_secret(
        &dh1,
        &dh2,
        &dh3,
        dh4.as_deref(),
        encapsulated,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    const DH1: Key = [0x11; 32];
    const DH2: Key = [0x22; 32];
    const DH3: Key = [0x33; 32];
    const DH4: Key = [0x44; 32];
    const SS: Key = [0x55; 32];

    /// The two signing purposes cannot be substituted for each other.
    ///
    /// Without the domain separation, `sign_message` and the handshake's
    /// prekey signing would be the same operation over the same input space,
    /// so a caller who could choose a "message" could obtain something a
    /// prekey verifier would accept, and vice versa.
    ///
    /// Both directions are checked, because tagging one side only works if it
    /// breaks both. The prekey side is deliberately untagged: its signature
    /// input is part of the external interoperability profile.
    #[test]
    fn signing_purposes_do_not_substitute_for_each_other() {
        let mut rng = rand_core::OsRng;
        let identity = Identity::generate(&mut rng);
        let public = identity.public();

        // The bytes a prekey signature covers: the tagged key form, untagged
        // by any purpose label.
        let prekey_input = encode_ec(&public);

        // A challenge answer over exactly those bytes.
        let challenge_sig = identity.sign_message(&prekey_input, &mut rng);
        assert!(
            verify_under_identity(&public, &prekey_input, &challenge_sig),
            "a challenge answer must verify as one"
        );
        assert!(
            xeddsa::verify(&public, &prekey_input, &challenge_sig).is_err(),
            "a challenge answer must not verify as a prekey signature"
        );

        // And the other way: a raw prekey-style signature over the same bytes.
        let prekey_sig = xeddsa::sign(&identity.export(), &prekey_input, &mut rng);
        assert!(
            xeddsa::verify(&public, &prekey_input, &prekey_sig).is_ok(),
            "a prekey signature must verify as one"
        );
        assert!(
            !verify_under_identity(&public, &prekey_input, &prekey_sig),
            "a prekey signature must not answer a challenge"
        );
    }

    #[test]
    fn one_time_prekey_changes_the_secret() {
        // The fourth Diffie-Hellman output is genuinely folded in, not dropped.
        let without = shared_secret(&DH1, &DH2, &DH3, None, &SS);
        let with = shared_secret(&DH1, &DH2, &DH3, Some(&DH4), &SS);
        assert_ne!(without, with);
    }

    #[test]
    fn encapsulated_secret_is_folded_in() {
        // A derivation that ignored ss would not be post-quantum forward secret.
        let a = shared_secret(&DH1, &DH2, &DH3, None, &SS);
        let b = shared_secret(&DH1, &DH2, &DH3, None, &[0x66; 32]);
        assert_ne!(a, b);
    }

    #[test]
    fn derivation_is_deterministic() {
        assert_eq!(
            shared_secret(&DH1, &DH2, &DH3, Some(&DH4), &SS),
            shared_secret(&DH1, &DH2, &DH3, Some(&DH4), &SS)
        );
    }

    #[test]
    fn order_of_inputs_matters() {
        // Swapping two Diffie-Hellman outputs must change the secret, otherwise
        // the concatenation would not bind their roles.
        assert_ne!(
            shared_secret(&DH1, &DH2, &DH3, None, &SS),
            shared_secret(&DH2, &DH1, &DH3, None, &SS)
        );
    }

    /// Build a signed bundle for the responder, from fixed secrets.
    fn make_bundle(
        ik_bytes: [u8; 32],
        spk_bytes: [u8; 32],
        opk: Option<dh::PublicKeyBytes>,
        kem_prekey: Vec<u8>,
    ) -> PreKeyBundle {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let ik = dh::PrivateKey::from_bytes(ik_bytes);
        let spk = dh::PrivateKey::from_bytes(spk_bytes);
        let spk_sig = xeddsa::sign(&ik_bytes, &encode_ec(&spk.public_key()), &mut rng);
        let kem_sig = xeddsa::sign(&ik_bytes, &encode_kem(&kem_prekey), &mut rng);
        PreKeyBundle {
            identity_key: ik.public_key(),
            signed_prekey: spk.public_key(),
            signed_prekey_signature: spk_sig,
            kem_prekey,
            kem_prekey_signature: kem_sig,
            one_time_prekey: opk,
        }
    }

    #[test]
    fn identity_key_serves_both_agreement_and_signing() {
        // ADR-0002 rests on one X25519 identity key being usable for both the
        // Diffie-Hellman agreements and the XEdDSA prekey signatures. If the
        // public key derived by each path differed, verification would fail.
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(1);
        let secret = [0x42u8; 32];
        let public = dh::PrivateKey::from_bytes(secret).public_key();
        let sig = xeddsa::sign(&secret, b"prekey", &mut rng);
        assert!(xeddsa::verify(&public, b"prekey", &sig).is_ok());
    }

    #[test]
    fn both_sides_agree_without_one_time_prekey() {
        let ik_b = [0x0bu8; 32];
        let spk_b = [0x0cu8; 32];
        let bundle = make_bundle(ik_b, spk_b, None, b"kem-public".to_vec());

        let ik_a = dh::PrivateKey::from_bytes([0x0au8; 32]);
        let ek_a = dh::PrivateKey::from_bytes([0x0eu8; 32]);
        let ss = [0x55u8; 32];

        let alice = initiator_shared_secret(&ik_a, &ek_a, &bundle, &ss).unwrap();
        let bob = responder_shared_secret(
            &dh::PrivateKey::from_bytes(ik_b),
            &dh::PrivateKey::from_bytes(spk_b),
            None,
            &ik_a.public_key(),
            &ek_a.public_key(),
            &ss,
        )
        .expect("test keys are not low-order");
        assert_eq!(alice, bob);
    }

    #[test]
    fn both_sides_agree_with_one_time_prekey() {
        let ik_b = [0x0bu8; 32];
        let spk_b = [0x0cu8; 32];
        let opk_b = dh::PrivateKey::from_bytes([0x0du8; 32]);
        let bundle = make_bundle(
            ik_b,
            spk_b,
            Some(opk_b.public_key()),
            b"kem-public".to_vec(),
        );

        let ik_a = dh::PrivateKey::from_bytes([0x0au8; 32]);
        let ek_a = dh::PrivateKey::from_bytes([0x0eu8; 32]);
        let ss = [0x55u8; 32];

        let alice = initiator_shared_secret(&ik_a, &ek_a, &bundle, &ss).unwrap();
        let bob = responder_shared_secret(
            &dh::PrivateKey::from_bytes(ik_b),
            &dh::PrivateKey::from_bytes(spk_b),
            Some(&opk_b),
            &ik_a.public_key(),
            &ek_a.public_key(),
            &ss,
        )
        .expect("test keys are not low-order");
        assert_eq!(alice, bob);
    }

    #[test]
    fn full_pqxdh_handshake_agrees() {
        // The whole handshake with a real ML-KEM prekey: Bob publishes, Alice
        // verifies and encapsulates, both derive, and the secrets match.
        use crate::primitives::kem;
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(11);

        let ik_b = [0x0bu8; 32];
        let spk_b = [0x0cu8; 32];
        let opk_b = dh::PrivateKey::from_bytes([0x0du8; 32]);
        let kem_kp = kem::KeyPair::generate(&mut rng);
        let bundle = make_bundle(ik_b, spk_b, Some(opk_b.public_key()), kem_kp.public_key());

        let ik_a = dh::PrivateKey::from_bytes([0x0au8; 32]);
        let ek_a = dh::PrivateKey::from_bytes([0x0eu8; 32]);

        let (ciphertext, ss_alice) = kem::encapsulate(&bundle.kem_prekey, &mut rng).unwrap();
        let alice = initiator_shared_secret(&ik_a, &ek_a, &bundle, &ss_alice).unwrap();

        let ss_bob = kem::decapsulate(&kem_kp, &ciphertext).unwrap();
        let bob = responder_shared_secret(
            &dh::PrivateKey::from_bytes(ik_b),
            &dh::PrivateKey::from_bytes(spk_b),
            Some(&opk_b),
            &ik_a.public_key(),
            &ek_a.public_key(),
            &ss_bob,
        )
        .expect("test keys are not low-order");

        assert_eq!(alice, bob, "both sides must derive the same shared secret");
    }

    #[test]
    fn a_forged_signed_prekey_is_rejected() {
        let mut bundle = make_bundle([0x0bu8; 32], [0x0cu8; 32], None, b"kem-public".to_vec());
        // Swap in a prekey the identity key never signed.
        bundle.signed_prekey = dh::PrivateKey::from_bytes([0x99u8; 32]).public_key();
        assert_eq!(
            verify_bundle(&bundle),
            Err(SessionError::BadSignedPrekeySignature)
        );
    }

    #[test]
    fn a_forged_kem_prekey_is_rejected() {
        let mut bundle = make_bundle([0x0bu8; 32], [0x0cu8; 32], None, b"kem-public".to_vec());
        bundle.kem_prekey = b"forged-kem-public".to_vec();
        assert_eq!(
            verify_bundle(&bundle),
            Err(SessionError::BadKemPrekeySignature)
        );
    }

    #[test]
    fn encodings_have_disjoint_ranges() {
        // A byte sequence must never be readable as both a curve key and a KEM
        // key, which the distinct leading bytes guarantee.
        let ec = encode_ec(&dh::PrivateKey::from_bytes([1u8; 32]).public_key());
        let kem = encode_kem(b"whatever");
        assert_ne!(ec[0], kem[0]);
    }

    /// The associated data is a bare concatenation, so it binds the two
    /// identities only because the first encoding has a width known in advance.
    /// This pins that width. If `encode_ec` ever became variable, two different
    /// pairs of identities could produce one associated data, and the binding
    /// would stop binding.
    ///
    /// `Proofs.SessionEstablishment` proves the recoverability from this fact
    /// and carries the counterexample for what happens without it.
    #[test]
    fn encode_ec_is_fixed_width() {
        let a = encode_ec(&dh::PublicKeyBytes::from_bytes([0x11; 32]));
        let b = encode_ec(&dh::PublicKeyBytes::from_bytes([0x22; 32]));
        assert_eq!(a.len(), 33, "one curve byte and a thirty-two byte key");
        assert_eq!(a.len(), b.len(), "the width cannot depend on the key");
    }

    #[test]
    fn associated_data_binds_both_identities_in_order() {
        assert_eq!(associated_data(b"alice", b"bob"), b"alicebob".to_vec());
        assert_eq!(
            associated_data_with_kem(b"alice", b"bob", b"pq"),
            b"alicebobpq".to_vec()
        );
    }
}
