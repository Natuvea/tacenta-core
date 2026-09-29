//! Byte-level session-establishment known answers.
//!
//! The full lifecycle and a reconstruction from the public leaf components
//! are deliberately separate paths. The first creates and consumes a real
//! prekey store through `establish_initiator`, `Session::encrypt`, and
//! `establish_responder`. The second computes the X25519 agreements, ML-KEM
//! encapsulation, PQXDH secret, split ratchet secrets, first message keys,
//! composite header, associated data, and AEAD output directly. Their outputs
//! must meet at the exact initial-message bytes recorded by the vector.
//!
//! Two vectors share this code. `one-time-prekeys-first-message` establishes
//! the responder from a torsion-spelled copy of the initial message and then
//! accepts the initiator's canonical repeat. `last-resort-first-message` is
//! the other direction on the path the replay record guards: the canonical
//! message establishes, and a replay of it in either spelling is refused, while
//! a repeat in a byte-different spelling of the same agreement is accepted.

use std::collections::{BTreeMap, VecDeque};

use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::montgomery::MontgomeryPoint;
use curve25519_dalek::traits::IsIdentity;
use rand_core::{CryptoRng, RngCore};

use super::{Vector, array32, bytes, eq, input, len_prefixed};
use tacenta_core::primitives::{aead, dh, kdf, kem};
use tacenta_core::serialization::composite::{AgreementType, Codeword, Composite};
use tacenta_core::{ratchet, serialization, sessions};

/// `LAST_RESORT_HANDSHAKE_LABEL` (CONSTANTS.md): the 32 ASCII bytes that key
/// the replay identity. Written out here, and not read from the crate, so that
/// the value the store records is checked against the specification's and not
/// against itself.
const LAST_RESORT_HANDSHAKE_LABEL: &[u8; 32] = b"tacenta last-resort handshake v2";

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

/// The seven other canonical u-coordinates in the agreement class of a curve
/// point: the point plus each non-zero multiple of the order-eight torsion
/// point `c7176a70...037a` (Edwards y), sorted byte-wise.
fn torsion_spellings(ephemeral: [u8; 32]) -> Vec<[u8; 32]> {
    let mut torsion_bytes = [0u8; 32];
    torsion_bytes.copy_from_slice(
        &hex::decode("c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a")
            .expect("order-eight torsion point"),
    );
    let torsion = CompressedEdwardsY(torsion_bytes)
        .decompress()
        .expect("order-eight torsion point decodes");
    assert!(torsion.is_small_order());
    assert!(!(torsion + torsion + torsion + torsion).is_identity());
    let point = MontgomeryPoint(ephemeral)
        .to_edwards(0)
        .expect("ephemeral has a Montgomery lift");
    let mut out = Vec::new();
    let mut multiple = torsion;
    for _ in 1..8 {
        let spelling = (point + multiple).to_montgomery().to_bytes();
        assert_ne!(spelling, ephemeral);
        assert!(spelling[31] < 0x80);
        out.push(spelling);
        multiple += torsion;
    }
    out.sort();
    out.dedup();
    assert_eq!(out.len(), 7);
    out
}

/// An initial message is `version(1) || type(1) || EncodeEC(identity) ||
/// EncodeEC(ephemeral) || ...` (message-format.md, Initial message), and
/// `EncodeEC` is a curve byte and a 32-byte key.
const EPHEMERAL_KEY: core::ops::Range<usize> = 36..68;

fn replace_at(message: &[u8], at: core::ops::Range<usize>, key: [u8; 32]) -> Vec<u8> {
    let mut message = message.to_vec();
    message[at].copy_from_slice(&key);
    message
}

fn replace_ephemeral(message: &[u8], spelling: [u8; 32]) -> Vec<u8> {
    replace_at(message, EPHEMERAL_KEY, spelling)
}

fn key_at(message: &[u8], at: core::ops::Range<usize>) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(&message[at]);
    out
}

fn ephemeral(message: &[u8]) -> [u8; 32] {
    key_at(message, EPHEMERAL_KEY)
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

/// Which of the two vectors is being computed.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Flow {
    /// One-time curve and KEM prekeys; the responder is established from a
    /// torsion-spelled copy and then accepts the canonical repeat.
    OneTime,
    /// Neither one-time prekey: the handshake names the last-resort KEM key
    /// and no one-time curve key, the path the replay record guards.
    LastResort,
}

/// The initiator's side, rebuilt from the public leaf components.
struct Rebuilt {
    dh1: Vec<u8>,
    dh2: Vec<u8>,
    dh3: Vec<u8>,
    dh4: Option<Vec<u8>>,
    kem_ciphertext: Vec<u8>,
    kem_secret: Vec<u8>,
    sk: [u8; 32],
    split_ec: [u8; 32],
    split_pq: [u8; 32],
    mk_ec: [u8; 32],
    mk_pq: [u8; 32],
    mk: [u8; 32],
    composite_bytes: Vec<u8>,
    ad: Vec<u8>,
    ciphertext: Vec<u8>,
    ratchet_message: Vec<u8>,
    initial: Vec<u8>,
}

/// Rebuild the KEM key and encapsulation from the named FIPS 203 d||z and m
/// draws, then the real X25519 agreements, PQXDH secret, split halves, first
/// message keys and the initial message, without the lifecycle.
fn rebuild(
    v: &Vector,
    flow: Flow,
    published: &sessions::PublishedBundle,
    alice: &sessions::Identity,
    bob: &sessions::Identity,
    plaintext: &[u8],
) -> Result<Rebuilt, String> {
    let kem_key_input = match flow {
        Flow::OneTime => "bob_one_time_kem_d_z",
        Flow::LastResort => "bob_last_resort_kem_d_z",
    };
    let mut kem_key_rng = ExactRng::new("KEM key generation", named(v, &[kem_key_input])?);
    let kem_pair = kem::KeyPair::generate(&mut kem_key_rng);
    kem_key_rng.finish()?;
    if kem_pair.public_key() != published.bundle.kem_prekey {
        return Err(format!(
            "the named {kem_key_input} does not produce the published key"
        ));
    }
    let mut kem_enc_rng = ExactRng::new(
        "ML-KEM encapsulation",
        named(v, &["alice_kem_encapsulation_m"])?,
    );
    let (kem_ciphertext, kem_secret) =
        kem::encapsulate(&kem_pair.public_key(), &mut kem_enc_rng)
            .map_err(|_| "ML-KEM encapsulation refused the generated public key".to_owned())?;
    kem_enc_rng.finish()?;

    let alice_identity = dh::PrivateKey::from_bytes(array32(&input(v, "alice_identity_secret")?)?);
    let alice_ephemeral =
        dh::PrivateKey::from_bytes(array32(&input(v, "alice_ephemeral_secret")?)?);
    let bob_signed = dh::PrivateKey::from_bytes(array32(&input(v, "bob_signed_prekey_secret")?)?);
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
    let dh4 = match flow {
        Flow::OneTime => {
            let bob_one_time =
                dh::PrivateKey::from_bytes(array32(&input(v, "bob_one_time_curve_secret")?)?);
            Some(
                alice_ephemeral
                    .agree(&bob_one_time.public_key())
                    .ok_or_else(non_contributory)?,
            )
        }
        Flow::LastResort => None,
    };
    let sk = sessions::shared_secret(&dh1, &dh2, &dh3, dh4.as_ref(), &kem_secret);
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
    let ciphertext = aead::encrypt(&enc, &mac, &iv, plaintext, &ad);
    let ratchet_message = serialization::encode_message(&composite, &ciphertext);
    let initial = serialization::encode_initial(
        &sessions::encode_ec(&alice.public()),
        &sessions::encode_ec(&alice_ephemeral.public_key()),
        &kem_ciphertext,
        published.signed_prekey_id,
        published.one_time_prekey_id,
        published.kem_prekey_id,
        &ratchet_message,
    );
    Ok(Rebuilt {
        dh1: dh1.to_vec(),
        dh2: dh2.to_vec(),
        dh3: dh3.to_vec(),
        dh4: dh4.map(|d| d.to_vec()),
        kem_ciphertext: kem_ciphertext.to_vec(),
        kem_secret: kem_secret.to_vec(),
        sk,
        split_ec,
        split_pq,
        mk_ec,
        mk_pq,
        mk,
        composite_bytes,
        ad,
        ciphertext,
        ratchet_message,
        initial,
    })
}

/// The replay records of a v5 prekey store, as `(kem_id, replay identity)`,
/// walked out of the stored bytes (session-persistence.md, Prekey store).
fn seen_entries(store: &[u8]) -> Result<Vec<(u32, [u8; 32])>, String> {
    let u32_at = |pos: usize| -> Result<u32, String> {
        store
            .get(pos..pos + 4)
            .map(|b| u32::from_be_bytes(b.try_into().unwrap()))
            .ok_or_else(|| format!("the store ends before {}", pos + 4))
    };
    if store.first() != Some(&5) {
        return Err("the recorded prekey store is not a v5 store".to_owned());
    }
    let one_time = u32_at(133)? as usize;
    let mut pos = 137 + one_time * 36;
    let (kem_at, kem_len) = len_prefixed(store, pos)?;
    pos = kem_at + kem_len + 4 + 64;
    let kem_one_time = u32_at(pos)? as usize;
    pos += 4;
    for _ in 0..kem_one_time {
        let (pair_at, pair_len) = len_prefixed(store, pos + 4)?;
        pos = pair_at + pair_len + 64;
    }
    pos += 4; // next_id
    let seen = u32_at(pos)? as usize;
    pos += 4;
    let mut out = Vec::with_capacity(seen);
    for _ in 0..seen {
        let id = u32_at(pos)?;
        let mut identity = [0u8; 32];
        identity.copy_from_slice(
            store
                .get(pos + 4..pos + 36)
                .ok_or_else(|| "the store ends inside a replay record".to_owned())?,
        );
        out.push((id, identity));
        pos += 36;
    }
    Ok(out)
}

fn expect_not_a_repeat(
    session: &mut sessions::Session,
    what: &str,
    message: &[u8],
) -> Result<(), String> {
    let before = session.export();
    let mut rng = ExactRng::new("refused repeated initial", vec![]);
    // An implementation that accepts the message goes on to decrypt it, which
    // draws randomness the vector does not state; the source stops the run
    // with a panic, and that is reported here as the acceptance it is.
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        session.decrypt(message, &mut rng)
    }))
    .map_err(|_| format!("{what} was accepted: the session went on to decrypt it"))?;
    rng.finish()?;
    if !matches!(refused, Err(sessions::LifecycleError::NotARepeatedInitial)) {
        return Err(format!("{what} was not refused as not a repeated initial"));
    }
    if session.export() != before {
        return Err(format!("{what} changed responder state"));
    }
    Ok(())
}

/// A wrapper the session recognises as a repeat, around a ratchet message it
/// has already read, yields no plaintext and changes nothing
/// (session-establishment.md, Receiving the initial message: the ratchet refuses
/// a message it has already accepted, "so a wrapper around a message already
/// read yields nothing"). The random draw the receive may take before it fails
/// is supplied and need not be used.
fn expect_no_plaintext(
    v: &Vector,
    session: &mut sessions::Session,
    what: &str,
    message: &[u8],
) -> Result<(), String> {
    let before = session.export();
    let mut rng = ExactRng::new(
        "repeat of a message already read",
        named(v, &["bob_repeat_random"])?,
    );
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        session.decrypt(message, &mut rng)
    }))
    .map_err(|_| format!("{what}: the receive drew more randomness than the vector states"))?;
    match outcome {
        Ok(_) => return Err(format!("{what} yielded a plaintext a second time")),
        Err(sessions::LifecycleError::NotARepeatedInitial) => {
            return Err(format!(
                "{what} was refused as not a repeat, not as already read"
            ));
        }
        Err(_) => {}
    }
    if session.export() != before {
        return Err(format!("{what} changed responder state"));
    }
    Ok(())
}

/// A message `establish_responder` must refuse, with the refusal named and the
/// prekey store left as it was. No random draw may precede the refusal.
fn expect_establish_refused(
    bob: &sessions::Identity,
    store: &mut sessions::PrekeyStore,
    what: &str,
    message: &[u8],
    refusal: &dyn Fn(&sessions::LifecycleError) -> bool,
) -> Result<(), String> {
    let before = store.to_bytes().to_vec();
    let mut rng = ExactRng::new("refused establishment", vec![]);
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        sessions::establish_responder(bob, store, message, &mut rng)
    }))
    .map_err(|_| format!("{what} was accepted: the responder went on to establish a session"))?;
    rng.finish()?;
    match refused {
        Err(error) if refusal(&error) => {}
        Err(error) => return Err(format!("{what} was refused as {error:?}")),
        Ok(_) => return Err(format!("{what} established a session")),
    }
    if store.to_bytes().to_vec() != before {
        return Err(format!("{what} changed the prekey store"));
    }
    Ok(())
}

fn observed(v: &Vector, flow: Flow) -> Result<BTreeMap<String, Vec<u8>>, String> {
    let alice_secret = array32(&input(v, "alice_identity_secret")?)?;
    let bob_secret = array32(&input(v, "bob_identity_secret")?)?;
    let plaintext = input(v, "plaintext")?;
    let repeat_plaintext = input(v, "repeat_plaintext")?;
    let alice = sessions::Identity::from_secret(alice_secret);
    let bob = sessions::Identity::from_secret(bob_secret);

    // Full lifecycle path: create a real store and carry one message through
    // both session constructors. Every random draw has a semantic name in the
    // vector and an exact call boundary here.
    let (one_time_count, prekey_draws): (usize, &[&str]) = match flow {
        Flow::OneTime => (
            1,
            &[
                "bob_signed_prekey_secret",
                "bob_signed_prekey_signature_nonce",
                "bob_one_time_curve_secret",
                "bob_last_resort_kem_d_z",
                "bob_last_resort_kem_signature_nonce",
                "bob_one_time_kem_d_z",
                "bob_one_time_kem_signature_nonce",
            ],
        ),
        Flow::LastResort => (
            0,
            &[
                "bob_signed_prekey_secret",
                "bob_signed_prekey_signature_nonce",
                "bob_last_resort_kem_d_z",
                "bob_last_resort_kem_signature_nonce",
            ],
        ),
    };
    let mut prekey_rng = ExactRng::new("prekey creation", named(v, prekey_draws)?);
    let mut store = bob.create_prekeys(one_time_count, &mut prekey_rng);
    prekey_rng.finish()?;
    let published = match flow {
        Flow::OneTime => store.publish(),
        Flow::LastResort => store.publish_multi_use(),
    };
    if flow == Flow::LastResort && published.one_time_prekey_id != serialization::ABSENT_ID {
        return Err("the last-resort bundle names a one-time curve prekey".to_owned());
    }
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

    // The initiator repeats the wrapper until it hears a response.  The
    // second initial carries a fresh inner ratchet message, so the responder
    // can check the byte-level repeat rule without relying on a fixture that
    // merely names the first message.
    let mut repeat_send_rng = ExactRng::new("initiator repeated send", vec![]);
    let repeat_initial = alice_session
        .encrypt(&repeat_plaintext, &mut repeat_send_rng)
        .map_err(|e| format!("repeated initial encrypt: {e:?}"))?;
    repeat_send_rng.finish()?;

    let torsion_initial = replace_ephemeral(&initial, torsion_spellings(ephemeral(&initial))[0]);
    let low_order_repeat = replace_ephemeral(&repeat_initial, [0u8; 32]);

    let mut out = BTreeMap::new();
    match flow {
        Flow::OneTime => {
            // The responder is established from the torsion-spelled copy, so
            // that its persisted `established_ephemeral` is not the spelling
            // the initiator's repeat carries.
            let mut responder_rng = ExactRng::new(
                "responder establishment",
                named(v, &["bob_ratchet_secret"])?,
            );
            let (mut bob_session, recovered) = sessions::establish_responder(
                &bob,
                &mut store,
                &torsion_initial,
                &mut responder_rng,
            )
            .map_err(|e| format!("responder establishment: {e:?}"))?;
            responder_rng.finish()?;
            if recovered != plaintext {
                return Err("the responder recovered a different first plaintext".to_owned());
            }
            let bob_state = bob_session.export();
            expect_not_a_repeat(
                &mut bob_session,
                "a low-order repeated initial",
                &low_order_repeat,
            )?;
            expect_no_plaintext(
                v,
                &mut bob_session,
                "the canonical message that the torsion-spelled one established",
                &initial,
            )?;
            let mut repeat_receive_rng = ExactRng::new(
                "responder repeated receive",
                named(v, &["bob_repeat_random"])?,
            );
            let repeated_recovered = bob_session
                .decrypt(&repeat_initial, &mut repeat_receive_rng)
                .map_err(|e| format!("repeated initial decrypt: {e:?}"))?;
            repeat_receive_rng.finish()?;
            if repeated_recovered != repeat_plaintext {
                return Err("the responder recovered a different repeated plaintext".to_owned());
            }
            let bob_repeat_state = bob_session.export();

            let rebuilt = rebuild(v, flow, &published, &alice, &bob, &plaintext)?;
            if rebuilt.initial != initial {
                return Err(
                    "the component reconstruction and lifecycle initial message differ".to_owned(),
                );
            }
            put_rebuilt(&mut out, &rebuilt);
            put(&mut out, "bundle", bundle_bytes);
            put(&mut out, "initial_message", &initial);
            put(&mut out, "torsion_initial", &torsion_initial);
            put(&mut out, "repeat_initial", &repeat_initial);
            put(&mut out, "low_order_repeat", &low_order_repeat);
            put(&mut out, "repeat_plaintext", repeated_recovered);
            put(&mut out, "alice_session_after_first_send", &*alice_state);
            put(&mut out, "bob_session_after_receipt", &*bob_state);
            put(&mut out, "bob_session_after_repeat", &*bob_repeat_state);
            put(
                &mut out,
                "bob_prekey_store_after_receipt",
                &*store.to_bytes(),
            );
            put(&mut out, "responder_plaintext", recovered);
        }
        Flow::LastResort => {
            let mut responder_rng = ExactRng::new(
                "responder establishment",
                named(v, &["bob_ratchet_secret"])?,
            );
            let (mut bob_session, recovered) =
                sessions::establish_responder(&bob, &mut store, &initial, &mut responder_rng)
                    .map_err(|e| format!("responder establishment: {e:?}"))?;
            responder_rng.finish()?;
            if recovered != plaintext {
                return Err("the responder recovered a different first plaintext".to_owned());
            }
            let bob_state = bob_session.export();
            let store_after_receipt = store.to_bytes().to_vec();

            let rebuilt = rebuild(v, flow, &published, &alice, &bob, &plaintext)?;
            if rebuilt.initial != initial {
                return Err(
                    "the component reconstruction and lifecycle initial message differ".to_owned(),
                );
            }

            // The store recorded exactly one replay identity, and it is
            // HMAC-SHA256 under the specification's label over the agreed SK:
            // written out here from the rebuilt SK, so a store that recorded
            // anything else (another key, another label, the public bytes)
            // is not this value.
            let replay_identity = kdf::hmac_sha256(LAST_RESORT_HANDSHAKE_LABEL, &rebuilt.sk);
            let recorded = seen_entries(&store_after_receipt)?;
            if recorded != vec![(published.kem_prekey_id, replay_identity)] {
                return Err(format!(
                    "the store recorded {recorded:?}, not the last-resort key's HMAC-SHA256 \
                     replay identity over SK"
                ));
            }

            // Replays of the spent handshake, in each spelling of the same
            // agreement, are the same handshake (session-establishment.md,
            // The replay identity): refused as replays, with nothing drawn and
            // nothing changed.
            let replayed = |e: &sessions::LifecycleError| {
                matches!(e, sessions::LifecycleError::ReplayedLastResort)
            };
            expect_establish_refused(
                &bob,
                &mut store,
                "a byte-identical replay",
                &initial,
                &replayed,
            )?;
            expect_establish_refused(
                &bob,
                &mut store,
                "a torsion-spelled replay",
                &torsion_initial,
                &replayed,
            )?;
            // A low-order ephemeral is no handshake at all: its agreement is
            // non-contributory, whatever the record holds.
            let low_order_initial = replace_ephemeral(&initial, [0u8; 32]);
            expect_establish_refused(
                &bob,
                &mut store,
                "a low-order initial message",
                &low_order_initial,
                &|e| {
                    matches!(
                        e,
                        sessions::LifecycleError::Handshake(
                            sessions::SessionError::NonContributoryAgreement
                        )
                    )
                },
            )?;

            // The wrapper of an established responder session: only the same
            // agreement class is a repeat.
            let unrelated =
                dh::PrivateKey::from_bytes(array32(&input(v, "unrelated_ephemeral_secret")?)?);
            let unrelated_repeat =
                replace_ephemeral(&repeat_initial, *unrelated.public_key().as_bytes());
            expect_not_a_repeat(
                &mut bob_session,
                "a low-order repeated initial",
                &low_order_repeat,
            )?;
            expect_not_a_repeat(
                &mut bob_session,
                "a repeated initial with an unrelated contributory ephemeral",
                &unrelated_repeat,
            )?;

            expect_no_plaintext(
                v,
                &mut bob_session,
                "the message that established the session, sent again",
                &initial,
            )?;

            // Both agreements non-contributory: an established_ephemeral that
            // is itself low-order imports, and a wrapper that matches it byte
            // for byte is still not a repeat.
            let mut low_established = bob_state.to_vec();
            let tail = low_established.len() - 33;
            if low_established[tail + 1..] != ephemeral(&initial) {
                return Err("the session does not end in the initiating ephemeral".to_owned());
            }
            low_established[tail + 1..].fill(0);
            let mut low_session = sessions::Session::import(&low_established)
                .map_err(|e| format!("a low-order established ephemeral was refused: {e:?}"))?;
            expect_not_a_repeat(
                &mut low_session,
                "a low-order repeated initial against a low-order established ephemeral",
                &low_order_repeat,
            )?;

            // Not only the spelling the vector records: every canonical
            // spelling of the initiator's ephemeral is the same agreement, so
            // each one replays the spent handshake and each one is a repeat.
            for spelling in torsion_spellings(ephemeral(&initial)) {
                expect_establish_refused(
                    &bob,
                    &mut store,
                    "a replay in another spelling of the agreement",
                    &replace_ephemeral(&initial, spelling),
                    &replayed,
                )?;
            }
            for spelling in torsion_spellings(ephemeral(&repeat_initial)) {
                let mut fresh = sessions::Session::import(&bob_state)
                    .map_err(|e| format!("the responder session does not import: {e:?}"))?;
                let mut rng = ExactRng::new(
                    "repeat in another spelling",
                    named(v, &["bob_repeat_random"])?,
                );
                let recovered = fresh
                    .decrypt(&replace_ephemeral(&repeat_initial, spelling), &mut rng)
                    .map_err(|e| format!("a repeat in another spelling was refused: {e:?}"))?;
                rng.finish()?;
                if recovered != repeat_plaintext {
                    return Err(
                        "a repeat in another spelling gave a different plaintext".to_owned()
                    );
                }
            }

            // The genuine repeat in a byte-different spelling of the same
            // agreement is accepted as the same agreement.
            let torsion_repeat = replace_ephemeral(
                &repeat_initial,
                torsion_spellings(ephemeral(&repeat_initial))[0],
            );
            let mut repeat_receive_rng = ExactRng::new(
                "responder repeated receive",
                named(v, &["bob_repeat_random"])?,
            );
            let repeated_recovered = bob_session
                .decrypt(&torsion_repeat, &mut repeat_receive_rng)
                .map_err(|e| format!("torsion-spelled repeat decrypt: {e:?}"))?;
            repeat_receive_rng.finish()?;
            if repeated_recovered != repeat_plaintext {
                return Err("the responder recovered a different repeated plaintext".to_owned());
            }
            let bob_repeat_state = bob_session.export();

            put_rebuilt(&mut out, &rebuilt);
            put(&mut out, "bundle", bundle_bytes);
            put(&mut out, "replay_identity", replay_identity);
            put(&mut out, "initial_message", &initial);
            put(&mut out, "torsion_initial", &torsion_initial);
            put(&mut out, "low_order_initial", &low_order_initial);
            put(&mut out, "repeat_initial", &repeat_initial);
            put(&mut out, "torsion_repeat", &torsion_repeat);
            put(&mut out, "low_order_repeat", &low_order_repeat);
            put(&mut out, "unrelated_repeat", &unrelated_repeat);
            put(&mut out, "repeat_plaintext", repeated_recovered);
            put(&mut out, "alice_session_after_first_send", &*alice_state);
            put(&mut out, "bob_session_after_receipt", &*bob_state);
            put(&mut out, "bob_session_after_repeat", &*bob_repeat_state);
            put(
                &mut out,
                "bob_session_low_order_established",
                &low_established,
            );
            put(
                &mut out,
                "bob_prekey_store_after_receipt",
                &store_after_receipt,
            );
            put(&mut out, "responder_plaintext", recovered);
        }
    }
    Ok(out)
}

/// The fields both vectors carry from the component reconstruction.
fn put_rebuilt(out: &mut BTreeMap<String, Vec<u8>>, rebuilt: &Rebuilt) {
    put(out, "dh1", &rebuilt.dh1);
    put(out, "dh2", &rebuilt.dh2);
    put(out, "dh3", &rebuilt.dh3);
    if let Some(dh4) = &rebuilt.dh4 {
        put(out, "dh4", dh4);
    }
    put(out, "kem_ciphertext", &rebuilt.kem_ciphertext);
    put(out, "kem_shared_secret", &rebuilt.kem_secret);
    put(out, "sk", rebuilt.sk);
    put(out, "split_ec", rebuilt.split_ec);
    put(out, "split_pq", rebuilt.split_pq);
    put(out, "mk_ec", rebuilt.mk_ec);
    put(out, "mk_pq", rebuilt.mk_pq);
    put(out, "mk", rebuilt.mk);
    put(out, "composite_header", &rebuilt.composite_bytes);
    put(out, "associated_data", &rebuilt.ad);
    put(out, "aead_output", &rebuilt.ciphertext);
    put(out, "ratchet_message", &rebuilt.ratchet_message);
}

fn flow_of(v: &Vector) -> Result<Flow, String> {
    match v.id.as_str() {
        "one-time-prekeys-first-message" => Ok(Flow::OneTime),
        "last-resort-first-message" => Ok(Flow::LastResort),
        other => Err(format!("no end-to-end session vector is named {other}")),
    }
}

pub(super) fn check(v: &Vector) -> Result<(), String> {
    let expected = v
        .fields
        .as_ref()
        .ok_or("the end-to-end session vector carries named output fields")?;
    let got = observed(v, flow_of(v)?)?;
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

    /// Prints regenerated named outputs for the committed input schedule of
    /// the vector named by `TACENTA_E2E_VECTOR` (the first vector when unset).
    /// Copying these into the vector is an explicit review step; ordinary CI
    /// only compares and never rewrites evidence.
    #[test]
    #[ignore = "prints regenerated session known-answer fields"]
    fn print_session_end_to_end_fields() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../vectors/session-establishment/session-e2e.json");
        let text = std::fs::read_to_string(path).unwrap();
        let file: super::super::VectorFile = serde_json::from_str(&text).unwrap();
        let wanted = std::env::var("TACENTA_E2E_VECTOR").ok();
        let vector = file
            .vectors
            .iter()
            .find(|v| wanted.as_deref().is_none_or(|id| v.id == id))
            .expect("the named end-to-end vector");
        let values = observed(vector, flow_of(vector).unwrap()).unwrap();
        let encoded: BTreeMap<_, _> = values
            .into_iter()
            .map(|(name, value)| (name, hex::encode(value)))
            .collect();
        println!("{}", serde_json::to_string_pretty(&encoded).unwrap());
    }
}
