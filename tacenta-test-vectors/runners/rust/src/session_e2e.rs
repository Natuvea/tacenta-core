//! One byte-level session-establishment known answer.
//!
//! The full lifecycle and a reconstruction from the public leaf components
//! are deliberately separate paths. The first creates and consumes a real
//! prekey store through `establish_initiator`, `Session::encrypt`, and
//! `establish_responder`. The second computes the four X25519 agreements,
//! ML-KEM encapsulation, PQXDH secret, split ratchet secrets, first message
//! keys, composite header, associated data, and AEAD output directly. Their
//! outputs must meet at the exact initial-message bytes recorded by the vector.

use std::collections::{BTreeMap, VecDeque};

use rand_core::{CryptoRng, RngCore};

use super::{Vector, array32, bytes, eq, input};
use tacenta_core::primitives::{aead, dh, kem};
use tacenta_core::serialization::composite::{AgreementType, Codeword, Composite};
use tacenta_core::{ratchet, serialization, sessions};

/// An RNG whose calls are themselves part of the vector. Each caller must ask
/// for the next chunk at exactly its stated length, and must consume them all.
struct ExactRng {
    name: &'static str,
    chunks: VecDeque<Vec<u8>>,
}

impl ExactRng {
    fn new(name: &'static str, chunks: Vec<Vec<u8>>) -> Self {
        Self {
            name,
            chunks: chunks.into(),
        }
    }

    fn finish(self) -> Result<(), String> {
        if self.chunks.is_empty() {
            Ok(())
        } else {
            Err(format!(
                "{} left {} random draw(s) unused",
                self.name,
                self.chunks.len()
            ))
        }
    }
}

impl RngCore for ExactRng {
    fn next_u32(&mut self) -> u32 {
        let mut out = [0u8; 4];
        self.fill_bytes(&mut out);
        u32::from_le_bytes(out)
    }

    fn next_u64(&mut self) -> u64 {
        let mut out = [0u8; 8];
        self.fill_bytes(&mut out);
        u64::from_le_bytes(out)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let chunk = self.chunks.pop_front().unwrap_or_else(|| {
            panic!(
                "{} requested an unstated {}-byte draw",
                self.name,
                dest.len()
            )
        });
        assert_eq!(
            chunk.len(),
            dest.len(),
            "{} requested {} random bytes where the next stated draw has {}",
            self.name,
            dest.len(),
            chunk.len()
        );
        dest.copy_from_slice(&chunk);
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl CryptoRng for ExactRng {}

fn named(v: &Vector, names: &[&str]) -> Result<Vec<Vec<u8>>, String> {
    names.iter().map(|name| input(v, name)).collect()
}

fn agreement_type(ty: tacenta_braid::MsgType) -> AgreementType {
    match ty {
        tacenta_braid::MsgType::None => AgreementType::None,
        tacenta_braid::MsgType::Hdr => AgreementType::Hdr,
        tacenta_braid::MsgType::Ek => AgreementType::Ek,
        tacenta_braid::MsgType::EkCt1Ack => AgreementType::EkCt1Ack,
        tacenta_braid::MsgType::Ct1 => AgreementType::Ct1,
        tacenta_braid::MsgType::Ct2 => AgreementType::Ct2,
    }
}

fn put(out: &mut BTreeMap<String, Vec<u8>>, name: &str, value: impl AsRef<[u8]>) {
    out.insert(name.to_owned(), value.as_ref().to_vec());
}

fn observed(v: &Vector) -> Result<BTreeMap<String, Vec<u8>>, String> {
    let alice_secret = array32(&input(v, "alice_identity_secret")?)?;
    let bob_secret = array32(&input(v, "bob_identity_secret")?)?;
    let plaintext = input(v, "plaintext")?;
    let alice = sessions::Identity::from_secret(alice_secret);
    let bob = sessions::Identity::from_secret(bob_secret);

    // Full lifecycle path: create a real store and carry one message through
    // both session constructors. Every random draw has a semantic name in the
    // vector and an exact call boundary here.
    let mut prekey_rng = ExactRng::new(
        "prekey creation",
        named(
            v,
            &[
                "bob_signed_prekey_secret",
                "bob_signed_prekey_signature_nonce",
                "bob_one_time_curve_secret",
                "bob_last_resort_kem_d_z",
                "bob_last_resort_kem_signature_nonce",
                "bob_one_time_kem_d_z",
                "bob_one_time_kem_signature_nonce",
            ],
        )?,
    );
    let mut store = bob.create_prekeys(1, &mut prekey_rng);
    prekey_rng.finish()?;
    let published = store.publish();
    let wire_bundle = serialization::WireBundle {
        identity_key: *published.bundle.identity_key.as_bytes(),
        signed_prekey: *published.bundle.signed_prekey.as_bytes(),
        signed_prekey_signature: published.bundle.signed_prekey_signature,
        kem_prekey: published.bundle.kem_prekey.clone(),
        kem_prekey_signature: published.bundle.kem_prekey_signature,
        one_time_prekey: published
            .bundle
            .one_time_prekey
            .as_ref()
            .map(|key| *key.as_bytes()),
        signed_prekey_id: published.signed_prekey_id,
        one_time_prekey_id: published.one_time_prekey_id,
        kem_prekey_id: published.kem_prekey_id,
    };
    let bundle_bytes = serialization::encode_bundle(&wire_bundle);

    let mut establish_rng = ExactRng::new(
        "initiator establishment",
        named(
            v,
            &[
                "alice_ephemeral_secret",
                "alice_kem_encapsulation_m",
                "alice_ratchet_secret",
            ],
        )?,
    );
    let mut alice_session = sessions::establish_initiator(&alice, &published, &mut establish_rng)
        .map_err(|e| format!("initiator establishment: {e:?}"))?;
    establish_rng.finish()?;

    let mut send_rng = ExactRng::new(
        "initiator first send",
        named(v, &["alice_braid_keygen_d_z"])?,
    );
    let initial = alice_session
        .encrypt(&plaintext, &mut send_rng)
        .map_err(|e| format!("first encrypt: {e:?}"))?;
    send_rng.finish()?;
    let alice_state = alice_session.export();

    let mut responder_rng = ExactRng::new(
        "responder establishment",
        named(v, &["bob_ratchet_secret"])?,
    );
    let (bob_session, recovered) =
        sessions::establish_responder(&bob, &mut store, &initial, &mut responder_rng)
            .map_err(|e| format!("responder establishment: {e:?}"))?;
    responder_rng.finish()?;
    if recovered != plaintext {
        return Err("the responder recovered a different first plaintext".to_owned());
    }
    let bob_state = bob_session.export();

    // Component reconstruction: rebuild the KEM key and encapsulation from the
    // named FIPS 203 d||z and m draws, then the four real X25519 agreements.
    let mut kem_key_rng = ExactRng::new(
        "one-time KEM key generation",
        named(v, &["bob_one_time_kem_d_z"])?,
    );
    let kem_pair = kem::KeyPair::generate(&mut kem_key_rng);
    kem_key_rng.finish()?;
    if kem_pair.public_key() != published.bundle.kem_prekey {
        return Err("the named one-time KEM d||z does not produce the published key".to_owned());
    }
    let mut kem_enc_rng = ExactRng::new(
        "ML-KEM encapsulation",
        named(v, &["alice_kem_encapsulation_m"])?,
    );
    let (kem_ciphertext, kem_secret) =
        kem::encapsulate(&kem_pair.public_key(), &mut kem_enc_rng)
            .map_err(|_| "ML-KEM encapsulation refused the generated public key".to_owned())?;
    kem_enc_rng.finish()?;

    let alice_identity = dh::PrivateKey::from_bytes(alice_secret);
    let alice_ephemeral =
        dh::PrivateKey::from_bytes(array32(&input(v, "alice_ephemeral_secret")?)?);
    let bob_signed = dh::PrivateKey::from_bytes(array32(&input(v, "bob_signed_prekey_secret")?)?);
    let bob_one_time =
        dh::PrivateKey::from_bytes(array32(&input(v, "bob_one_time_curve_secret")?)?);
    let non_contributory = || "a named X25519 agreement was non-contributory".to_owned();
    let dh1 = alice_identity
        .agree(&bob_signed.public_key())
        .ok_or_else(non_contributory)?;
    let dh2 = alice_ephemeral
        .agree(&bob.public())
        .ok_or_else(non_contributory)?;
    let dh3 = alice_ephemeral
        .agree(&bob_signed.public_key())
        .ok_or_else(non_contributory)?;
    let dh4 = alice_ephemeral
        .agree(&bob_one_time.public_key())
        .ok_or_else(non_contributory)?;
    let sk = sessions::shared_secret(&dh1, &dh2, &dh3, Some(&dh4), &kem_secret);
    let (split_ec, split_pq) = tacenta_triple::split_secret(&sk);

    // Reconstruct the first agreement message and both ratchet message keys.
    let mut braid_rng = ExactRng::new(
        "reconstructed Braid send",
        named(v, &["alice_braid_keygen_d_z"])?,
    );
    let braid = tacenta_braid::Braid::initiator(&sk);
    let (agreement, sending_epoch, agreement_output, _) = braid.send(&mut braid_rng);
    braid_rng.finish()?;
    if agreement_output.is_some() {
        return Err("the first Braid send unexpectedly produced an epoch key".to_owned());
    }

    let alice_ratchet = dh::PrivateKey::from_bytes(array32(&input(v, "alice_ratchet_secret")?)?);
    let ratchet_dh = alice_ratchet
        .agree(&bob_signed.public_key())
        .ok_or_else(non_contributory)?;
    let mut classical = ratchet::init_sender(
        &split_ec,
        *alice_ratchet.public_key().as_bytes(),
        *bob_signed.public_key().as_bytes(),
        &ratchet_dh,
        ratchet::LabelSet::Tacenta,
    );
    let (classical_header, mk_ec) = ratchet::send(&mut classical)
        .map_err(|e| format!("reconstructed classical send: {e:?}"))?;
    let mut sparse = tacenta_spqr::State::init_alice(&split_pq);
    let (pq_n, mk_pq) = sparse
        .send(sending_epoch, None)
        .map_err(|e| format!("reconstructed sparse send: {e:?}"))?;
    let mk = tacenta_triple::combine(&mk_ec, &mk_pq);
    let composite = Composite {
        dh: classical_header.dh,
        pn: classical_header.pn,
        n: classical_header.n,
        pq_epoch: sending_epoch,
        pq_n,
        ag_epoch: agreement.epoch,
        ag_type: agreement_type(agreement.ty),
        ag_chunk: agreement.data.map(|chunk| Codeword {
            index: chunk.index,
            data: chunk.data,
        }),
    };
    let composite_bytes = tacenta_core::serialization::composite::encode_composite(&composite);
    let identity_ad = sessions::associated_data(
        &sessions::encode_ec(&alice.public()),
        &sessions::encode_ec(&bob.public()),
    );
    let ad = serialization::concat_ad(&identity_ad, &composite);
    let (enc, mac, iv) = ratchet::message_keys(&mk, ratchet::LabelSet::Tacenta);
    let ciphertext = aead::encrypt(&enc, &mac, &iv, &plaintext, &ad);
    let ratchet_message = serialization::encode_message(&composite, &ciphertext);
    let reconstructed_initial = serialization::encode_initial(
        &sessions::encode_ec(&alice.public()),
        &sessions::encode_ec(&alice_ephemeral.public_key()),
        &kem_ciphertext,
        published.signed_prekey_id,
        published.one_time_prekey_id,
        published.kem_prekey_id,
        &ratchet_message,
    );
    if reconstructed_initial != initial {
        return Err("the component reconstruction and lifecycle initial message differ".to_owned());
    }

    let mut out = BTreeMap::new();
    put(&mut out, "bundle", bundle_bytes);
    put(&mut out, "dh1", dh1);
    put(&mut out, "dh2", dh2);
    put(&mut out, "dh3", dh3);
    put(&mut out, "dh4", dh4);
    put(&mut out, "kem_ciphertext", kem_ciphertext);
    put(&mut out, "kem_shared_secret", kem_secret);
    put(&mut out, "sk", sk);
    put(&mut out, "split_ec", split_ec);
    put(&mut out, "split_pq", split_pq);
    put(&mut out, "mk_ec", mk_ec);
    put(&mut out, "mk_pq", mk_pq);
    put(&mut out, "mk", mk);
    put(&mut out, "composite_header", composite_bytes);
    put(&mut out, "associated_data", ad);
    put(&mut out, "aead_output", ciphertext);
    put(&mut out, "ratchet_message", ratchet_message);
    put(&mut out, "initial_message", initial);
    put(&mut out, "alice_session_after_first_send", &*alice_state);
    put(&mut out, "bob_session_after_receipt", &*bob_state);
    put(
        &mut out,
        "bob_prekey_store_after_receipt",
        &*store.to_bytes(),
    );
    put(&mut out, "responder_plaintext", recovered);
    Ok(out)
}

pub(super) fn check(v: &Vector) -> Result<(), String> {
    let expected = v
        .fields
        .as_ref()
        .ok_or("the end-to-end session vector carries named output fields")?;
    let got = observed(v)?;
    if got.len() != expected.len() {
        return Err(format!(
            "computed {} output fields, vector names {}",
            got.len(),
            expected.len()
        ));
    }
    for (name, got_value) in got {
        let expected_hex = expected
            .get(&name)
            .ok_or_else(|| format!("the vector has no expected {name}"))?;
        eq(&got_value, &bytes(expected_hex)?).map_err(|e| format!("field {name}: {e}"))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    /// Prints regenerated named outputs for the committed input schedule.
    /// Copying these into the vector is an explicit review step; ordinary CI
    /// only compares and never rewrites evidence.
    #[test]
    #[ignore = "prints regenerated session known-answer fields"]
    fn print_session_end_to_end_fields() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../vectors/session-establishment/session-e2e.json");
        let text = std::fs::read_to_string(path).unwrap();
        let file: super::super::VectorFile = serde_json::from_str(&text).unwrap();
        let values = observed(&file.vectors[0]).unwrap();
        let encoded: BTreeMap<_, _> = values
            .into_iter()
            .map(|(name, value)| (name, hex::encode(value)))
            .collect();
        println!("{}", serde_json::to_string_pretty(&encoded).unwrap());
    }
}
