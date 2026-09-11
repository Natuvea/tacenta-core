//! Rust conformance runner. Loads the shared, language-agnostic test-vector
//! files and drives tacenta-core against them, so the same vectors that check
//! every language runner check this one. Vector format: schema/vector.schema.json.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use serde::Deserialize;

use tacenta_core::ratchet;

/// One vector file (one algorithm), matching schema/vector.schema.json.
#[derive(Deserialize)]
pub struct VectorFile {
    pub schema_version: u32,
    pub algorithm: String,
    pub source: String,
    pub vectors: Vec<Vector>,
}

#[derive(Deserialize)]
pub struct Vector {
    pub id: String,
    #[serde(default)]
    pub comment: String,
    #[serde(default = "valid")]
    pub result: String,
    pub inputs: BTreeMap<String, String>,
    #[serde(default)]
    pub output: String,
    /// A decoder's answer: the named values an accepted input decodes to,
    /// carried in place of `output` (schema/vector.schema.json).
    #[serde(default)]
    pub fields: Option<BTreeMap<String, String>>,
}

fn valid() -> String {
    "valid".to_string()
}

/// Whether the vector expects the operation to succeed.
fn expects_success(v: &Vector) -> Result<bool, String> {
    match v.result.as_str() {
        "valid" => Ok(true),
        "invalid" => Ok(false),
        unknown => Err(format!("unknown result {unknown}")),
    }
}

/// Load every `*.json` vector file in `dir`.
pub fn load_dir(dir: &Path) -> Result<Vec<VectorFile>, String> {
    let mut files = Vec::new();
    let entries = fs::read_dir(dir).map_err(|e| format!("read {}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.extension().and_then(|e| e.to_str()) == Some("json") {
            let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            let file: VectorFile =
                serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
            files.push(file);
        }
    }
    Ok(files)
}

/// Check every vector in a file, returning the number checked.
pub fn check_file(file: &VectorFile) -> Result<usize, String> {
    if file.schema_version != 1 {
        return Err(format!(
            "unsupported schema_version {}",
            file.schema_version
        ));
    }
    for v in &file.vectors {
        check_vector(&file.algorithm, v)
            .map_err(|e| format!("{} [{}]: {e}", file.algorithm, v.id))?;
    }
    Ok(file.vectors.len())
}

/// A single field element, two bytes big-endian.
fn bv16(bytes: &[u8]) -> Result<u16, String> {
    if bytes.len() != 2 {
        return Err(format!("expected 2 bytes, got {}", bytes.len()));
    }
    Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
}

/// A run of field elements, two bytes each.
fn bv16s(bytes: &[u8]) -> Result<Vec<u16>, String> {
    if !bytes.len().is_multiple_of(2) {
        return Err(format!("expected an even length, got {}", bytes.len()));
    }
    let (pairs, _rest) = bytes.as_chunks::<2>();
    Ok(pairs.iter().map(|&c| u16::from_be_bytes(c)).collect())
}

/// A counter, eight bytes big-endian, as both models encode them.
fn be64(bytes: &[u8]) -> Result<u64, String> {
    let a: [u8; 8] = bytes
        .try_into()
        .map_err(|_| format!("expected 8 bytes, got {}", bytes.len()))?;
    Ok(u64::from_be_bytes(a))
}

fn check_vector(algorithm: &str, v: &Vector) -> Result<(), String> {
    use tacenta_core::primitives::{dh, kdf};
    use tacenta_core::sessions;

    match algorithm {
        "message-encoding" => {
            use tacenta_core::serialization;
            let header = composite_from(v)?;
            eq(
                &serialization::encode_message(&header, &input(v, "ciphertext")?),
                &bytes(&v.output)?,
            )
        }
        "initial-message-encoding" => {
            use tacenta_core::serialization;
            eq(
                &serialization::encode_initial(
                    &input(v, "identity")?,
                    &input(v, "ephemeral")?,
                    &input(v, "kem_ciphertext")?,
                    be32(&input(v, "signed_prekey_id")?)?,
                    be32(&input(v, "one_time_prekey_id")?)?,
                    be32(&input(v, "kem_prekey_id")?)?,
                    &input(v, "ratchet_message")?,
                ),
                &bytes(&v.output)?,
            )
        }
        "pqxdh-sk" => {
            let dh1 = array32(&input(v, "dh1")?)?;
            let dh2 = array32(&input(v, "dh2")?)?;
            let dh3 = array32(&input(v, "dh3")?)?;
            let ss = array32(&input(v, "ss")?)?;
            // dh4 is present exactly when the bundle carried a one-time curve prekey.
            let dh4 = match v.inputs.get("dh4") {
                Some(_) => Some(array32(&input(v, "dh4")?)?),
                None => None,
            };
            eq(
                &sessions::shared_secret(&dh1, &dh2, &dh3, dh4.as_ref(), &ss),
                &bytes(&v.output)?,
            )
        }
        "hkdf-sha256" => {
            let expected = bytes(&v.output)?;
            let mut out = vec![0u8; expected.len()];
            kdf::hkdf_sha256_into(
                &input(v, "salt")?,
                &input(v, "ikm")?,
                &input(v, "info")?,
                &mut out,
            );
            eq(&out, &expected)
        }
        "hmac-sha256" => eq(
            &kdf::hmac_sha256(&input(v, "key")?, &input(v, "data")?),
            &bytes(&v.output)?,
        ),
        "x25519" => {
            let secret = array32(&input(v, "private")?)?;
            let peer = dh::PublicKeyBytes::from_bytes(array32(&input(v, "peer_public")?)?);
            // `agree` refuses a low-order peer key rather than returning the
            // all-zero secret it would otherwise produce. No RFC 7748 vector
            // exercises that, but a vector file could, and "the primitive
            // refused" is a distinct outcome from "the bytes differed".
            match dh::PrivateKey::from_bytes(secret).agree(&peer) {
                Some(shared) => eq(&shared, &bytes(&v.output)?),
                None => Err("agreement refused: the peer key is low-order".to_owned()),
            }
        }
        // Ed25519 is a trusted-boundary primitive, not a tacenta-core API:
        // the core exposes no Ed25519 signing of its own, and `xeddsa::verify`
        // checks with `ed25519_dalek::VerifyingKey::verify_strict`. So the
        // RFC 8032 vectors are checked against that crate directly, at the
        // version this runner's lockfile pins, which is the same version and
        // build tacenta-core links.
        "ed25519" => {
            use ed25519_dalek::{Signer, SigningKey};
            let key = SigningKey::from_bytes(&array32(&input(v, "secret")?)?);
            let message = input(v, "message")?;
            let sig = key.sign(&message);
            eq(&sig.to_bytes(), &bytes(&v.output)?)?;
            key.verifying_key()
                .verify_strict(&message, &sig)
                .map_err(|_| "the signature does not verify".to_string())
        }
        // XEdDSA is randomised: the signer draws 64 bytes of `Z`. The vector
        // supplies those bytes as `nonce`, served by a byte source that
        // repeats them, so the signature is a fixed function of key, message
        // and nonce and the expected bytes can be pinned. The verification
        // that follows is the half that does not depend on this crate's own
        // word: `verify` checks with an independent Ed25519 implementation.
        //
        // A vector that carries a `signature` input instead is verify-only:
        // a public key `u`, a message and a signature that `verify` must
        // refuse (`result: invalid`) or accept (`result: valid`, with the
        // output the compressed Edwards key it verified under). These pin
        // the edges of the accepted set, where this verifier and XEdDSA
        // Revision 1 differ by design; each vector's comment says which way
        // Revision 1 goes, and a test in tacenta-core holds the comments to a
        // transcription of the specification's own verifier, and that
        // transcription to ed25519-dalek's non-strict verify.
        "xeddsa" => {
            use tacenta_core::primitives::xeddsa;
            let message = input(v, "message")?;
            if v.inputs.contains_key("signature") {
                let public = dh::PublicKeyBytes::from_bytes(array32(&input(v, "public")?)?);
                let signature: [u8; 64] = input(v, "signature")?
                    .try_into()
                    .map_err(|_| "expected a 64-byte signature".to_string())?;
                let outcome = xeddsa::verify(&public, &message, &signature);
                return match (v.result.as_str(), outcome) {
                    ("invalid", Err(_)) => Ok(()),
                    ("invalid", Ok(())) => {
                        Err("accepted a signature the vector refuses".to_string())
                    }
                    ("valid", Err(_)) => Err("refused a signature the vector accepts".to_string()),
                    ("valid", Ok(())) => {
                        let key = xeddsa::verifying_key(&public, &signature)
                            .map_err(|_| "verified, yet the key does not convert".to_string())?;
                        eq(&key, &bytes(&v.output)?)
                    }
                    (other, _) => Err(format!("unknown result {other}")),
                };
            }
            let secret = array32(&input(v, "secret")?)?;
            let mut rng = FixedBytes::new(input(v, "nonce")?)?;
            let sig = xeddsa::sign(&secret, &message, &mut rng);
            eq(&sig, &bytes(&v.output)?)?;
            let public = dh::PrivateKey::from_bytes(secret).public_key();
            xeddsa::verify(&public, &message, &sig)
                .map_err(|_| "the signature does not verify".to_string())
        }
        // The post-quantum derivations. These crates were transcribed from the
        // models by hand, and these are what pin the transcription: a label, a
        // counter encoding, or a salt and keying material the wrong way round
        // all show up here and nowhere else.
        "gf65536-mul" => {
            let a = bv16(&input(v, "a")?)?;
            let b = bv16(&input(v, "b")?)?;
            eq(
                &tacenta_erasure::gf::mul(a, b).to_be_bytes(),
                &bytes(&v.output)?,
            )
        }
        "gf65536-inv" => {
            let a = bv16(&input(v, "a")?)?;
            eq(
                &tacenta_erasure::gf::inv(a).to_be_bytes(),
                &bytes(&v.output)?,
            )
        }
        "polynomial-interp" => {
            let nodes = bv16s(&input(v, "nodes")?)?;
            let values = bv16s(&input(v, "values")?)?;
            let x = bv16(&input(v, "x")?)?;
            eq(
                &tacenta_erasure::interpolate(&nodes, &values, x).to_be_bytes(),
                &bytes(&v.output)?,
            )
        }
        "spqr-kdf-ck" => {
            let ck = array32(&input(v, "ck")?)?;
            let n = be64(&input(v, "n")?)?;
            let (next, mk) = tacenta_spqr::kdf_ck(&ck, n);
            eq(
                &[next.as_slice(), mk.as_slice()].concat(),
                &bytes(&v.output)?,
            )
        }
        "braid-kdf-ok" => {
            let ss = input(v, "ss")?;
            let epoch = be64(&input(v, "epoch")?)?;
            eq(&tacenta_braid::kdf_ok(&ss, epoch), &bytes(&v.output)?)
        }
        "braid-auth-update" => {
            let root = array32(&input(v, "root")?)?;
            let key = array32(&input(v, "key")?)?;
            let epoch = be64(&input(v, "epoch")?)?;
            let mut auth = tacenta_braid::Auth::from_root(root);
            auth.update(epoch, &key);
            let (r, m) = auth.keys();
            eq(&[r.as_slice(), m.as_slice()].concat(), &bytes(&v.output)?)
        }
        "triple-combine" => {
            let a = array32(&input(v, "mk_ec")?)?;
            let b = array32(&input(v, "mk_pq")?)?;
            eq(&tacenta_triple::combine(&a, &b), &bytes(&v.output)?)
        }
        "triple-split" => {
            let sk = input(v, "sk")?;
            let (ec, pq) = tacenta_triple::split_secret(&sk);
            eq(&[ec.as_slice(), pq.as_slice()].concat(), &bytes(&v.output)?)
        }
        "composite-header" => {
            use tacenta_core::serialization::composite as c;
            let h = composite_from(v)?;
            let encoded = c::encode_composite(&h);
            eq(&encoded, &bytes(&v.output)?)?;
            // And the decoder agrees with the encoder, which is the model's
            // round-trip theorem checked on the implementation.
            let (back, rest) = c::decode_composite(&encoded).map_err(|e| format!("{e:?}"))?;
            if back != h || !rest.is_empty() {
                return Err("round trip disagreed".to_string());
            }
            Ok(())
        }
        // The erasure code above the field: chunking, the systematic and
        // parity codewords, the stream's end, and decoding from what arrived,
        // first copy winning (mlkem-braid.md, The erasure code).
        "erasure-encode" => check_erasure_encode(v),
        "erasure-decode" => check_erasure_decode(v),
        // The two coders' persisted formats and the rules their readers apply
        // (session-persistence.md, Erasure coder sub-formats).
        "erasure-encoder-state" => check_encoder_state(v),
        "erasure-decoder-state" => check_decoder_state(v),
        // The bounded protobuf profile's two readers (protobuf-profile.md).
        "protobuf-ratchet-body" => check_ratchet_body(v),
        "protobuf-prekey-envelope" => check_prekey_envelope(v),
        // The AEAD (message-format.md, Authenticated encryption).
        "aead-encrypt" => check_aead_encrypt(v),
        "aead-decrypt" => check_aead_decrypt(v),
        other => Err(format!("no runner for algorithm {other}")),
    }
}

/// A run of codewords as the vectors write them: `index(2) || chunk(32)`
/// each, in the order they arrive.
fn erasure_codewords(bytes: &[u8]) -> Result<Vec<tacenta_erasure::Chunk>, String> {
    use tacenta_erasure::{CHUNK_BYTES, Chunk};
    if !bytes.len().is_multiple_of(2 + CHUNK_BYTES) {
        return Err(format!(
            "codewords: {} bytes is not a whole number of codewords",
            bytes.len()
        ));
    }
    bytes
        .chunks_exact(2 + CHUNK_BYTES)
        .map(|c| {
            Ok(Chunk {
                index: u16::from_be_bytes([c[0], c[1]]),
                data: c[2..].try_into().map_err(|_| "codeword data".to_string())?,
            })
        })
        .collect()
}

/// A fresh encoder's codewords at the listed indices. The encoder is run from
/// index 0, and each codeword it issues must carry the next index; with
/// `stream_length`, it is then run to its end and must issue exactly that
/// many in all.
fn check_erasure_encode(v: &Vector) -> Result<(), String> {
    use tacenta_erasure::Encoder;
    let message = input(v, "message")?;
    let indices = bv16s(&input(v, "indices")?)?;
    let last = indices.iter().copied().max().ok_or("no indices")?;
    let mut enc = Encoder::new(&message);
    let mut issued = Vec::with_capacity(usize::from(last) + 1);
    for expected in 0..=last {
        let chunk = enc
            .next_chunk()
            .ok_or_else(|| format!("the stream ended before index {expected}"))?;
        if chunk.index != expected {
            return Err(format!(
                "issued index {} where {expected} was next",
                chunk.index
            ));
        }
        issued.push(chunk.data);
    }
    let got: Vec<u8> = indices
        .iter()
        .flat_map(|&i| issued[usize::from(i)])
        .collect();
    eq(&got, &bytes(&v.output)?)?;
    if v.inputs.contains_key("stream_length") {
        let want = be32(&input(v, "stream_length")?)? as usize;
        let mut total = issued.len();
        while enc.next_chunk().is_some() {
            total += 1;
        }
        if total != want {
            return Err(format!("the stream issued {total} codewords, not {want}"));
        }
    }
    Ok(())
}

/// A decoder for `size` bytes offered the listed codewords in order: the
/// value, or no value for an invalid vector.
fn check_erasure_decode(v: &Vector) -> Result<(), String> {
    use tacenta_erasure::Decoder;
    let size = be32(&input(v, "size")?)? as usize;
    let mut dec = Decoder::new(size);
    for c in erasure_codewords(&input(v, "codewords")?)? {
        dec.add_chunk(c);
    }
    match (expects_success(v)?, dec.message()) {
        (true, Some(m)) => eq(&m, &bytes(&v.output)?),
        (true, None) => Err("the decoder holds no value; the vector has one".to_string()),
        (false, None) if !dec.has_message() => Ok(()),
        (false, _) => Err("the decoder holds a value; the vector has none".to_string()),
    }
}

/// An encoder's stored bytes. Either built by operations (`message`,
/// `issued`) and then written, read back to the same encoder, and continued
/// to the same next codeword; or offered as `bytes` to the reader, which
/// accepts them, writing back the output, or refuses them.
fn check_encoder_state(v: &Vector) -> Result<(), String> {
    use tacenta_erasure::Encoder;
    if v.inputs.contains_key("bytes") {
        let stored = input(v, "bytes")?;
        return match (expects_success(v)?, Encoder::from_bytes(&stored)) {
            (true, Some(e)) => eq(&e.to_bytes(), &bytes(&v.output)?),
            (true, None) => Err("refused stored bytes the vector accepts".to_string()),
            (false, None) => Ok(()),
            (false, Some(_)) => Err("accepted stored bytes the vector refuses".to_string()),
        };
    }
    let message = input(v, "message")?;
    let issued = be32(&input(v, "issued")?)?;
    let mut enc = Encoder::new(&message);
    for i in 0..issued {
        enc.next_chunk()
            .ok_or_else(|| format!("the stream ended after {i} codewords"))?;
    }
    let stored = enc.to_bytes();
    eq(&stored, &bytes(&v.output)?)?;
    let mut back =
        Encoder::from_bytes(&stored).ok_or("the reader refuses what the writer wrote")?;
    if back != enc {
        return Err("read back a different encoder".to_string());
    }
    if back.next_chunk() != enc.next_chunk() {
        return Err("the encoder read back issues a different next codeword".to_string());
    }
    Ok(())
}

/// A decoder's stored bytes, the same two ways as `check_encoder_state`; a
/// decoder built by operations, read back, must still reach the same value.
fn check_decoder_state(v: &Vector) -> Result<(), String> {
    use tacenta_erasure::Decoder;
    if v.inputs.contains_key("bytes") {
        let stored = input(v, "bytes")?;
        return match (expects_success(v)?, Decoder::from_bytes(&stored)) {
            (true, Some(d)) => eq(&d.to_bytes(), &bytes(&v.output)?),
            (true, None) => Err("refused stored bytes the vector accepts".to_string()),
            (false, None) => Ok(()),
            (false, Some(_)) => Err("accepted stored bytes the vector refuses".to_string()),
        };
    }
    let size = be32(&input(v, "size")?)? as usize;
    let mut dec = Decoder::new(size);
    for c in erasure_codewords(&input(v, "codewords")?)? {
        dec.add_chunk(c);
    }
    let stored = dec.to_bytes();
    eq(&stored, &bytes(&v.output)?)?;
    let back = Decoder::from_bytes(&stored).ok_or("the reader refuses what the writer wrote")?;
    if back != dec || back.message() != dec.message() {
        return Err("read back a different decoder".to_string());
    }
    Ok(())
}

/// The decoded values against the vector's `fields`: the same names, and the
/// same bytes. A value decoded as absent (`None`) must be absent from the
/// vector, and the vector may name nothing that was not decoded.
fn fields_eq(v: &Vector, got: &[(&str, Option<Vec<u8>>)]) -> Result<(), String> {
    let want = v
        .fields
        .as_ref()
        .ok_or("a valid decoder vector carries fields")?;
    for (name, value) in got {
        match (value, want.get(*name)) {
            (Some(g), Some(w)) => eq(g, &bytes(w)?).map_err(|e| format!("{name}: {e}"))?,
            (None, None) => {}
            (Some(_), None) => {
                return Err(format!("decoded {name}, which the vector does not have"));
            }
            (None, Some(_)) => {
                return Err(format!("the vector has {name}, which was not decoded"));
            }
        }
    }
    match want.keys().find(|k| !got.iter().any(|(n, _)| n == k)) {
        Some(extra) => Err(format!(
            "the vector names {extra}, which no decoder field is"
        )),
        None => Ok(()),
    }
}

fn check_ratchet_body(v: &Vector) -> Result<(), String> {
    let region = input(v, "region")?;
    match (
        expects_success(v)?,
        tacenta_protobuf::parse_ratchet_body(region),
    ) {
        (true, Ok(b)) => fields_eq(
            v,
            &[
                ("ratchet_key", Some(b.ratchet_key)),
                ("counter", Some(b.counter.to_be_bytes().to_vec())),
                (
                    "previous_counter",
                    Some(b.previous_counter.to_be_bytes().to_vec()),
                ),
                ("ciphertext", Some(b.ciphertext)),
                ("pq", Some(b.pq)),
            ],
        ),
        (true, Err(e)) => Err(format!("refused ({e:?}) a region the vector accepts")),
        (false, Err(_)) => Ok(()),
        (false, Ok(_)) => Err("accepted a region the vector refuses".to_string()),
    }
}

fn check_prekey_envelope(v: &Vector) -> Result<(), String> {
    let region = input(v, "region")?;
    match (
        expects_success(v)?,
        tacenta_protobuf::parse_prekey_body(region),
    ) {
        (true, Ok(b)) => fields_eq(
            v,
            &[
                ("prekey_id", b.prekey_id.map(|i| i.to_be_bytes().to_vec())),
                ("base_key", Some(b.base_key)),
                ("identity_key", Some(b.identity_key)),
                ("message", Some(b.message)),
                (
                    "registration_id",
                    Some(b.registration_id.to_be_bytes().to_vec()),
                ),
                (
                    "signed_prekey_id",
                    Some(b.signed_prekey_id.to_be_bytes().to_vec()),
                ),
                ("pq_prekey_id", Some(b.pq_prekey_id.to_be_bytes().to_vec())),
                ("kem", Some(b.kem)),
            ],
        ),
        (true, Err(e)) => Err(format!("refused ({e:?}) a region the vector accepts")),
        (false, Err(_)) => Ok(()),
        (false, Ok(_)) => Err("accepted a region the vector refuses".to_string()),
    }
}

/// The AEAD key, the MAC key and the IV.
type AeadKeys = ([u8; 32], [u8; 32], [u8; 16]);

/// The AEAD's three keys, in the shape the message-key expansion hands them
/// over.
fn aead_keys(v: &Vector) -> Result<AeadKeys, String> {
    let iv: [u8; 16] = input(v, "iv")?
        .try_into()
        .map_err(|_| "expected a 16-byte iv".to_string())?;
    Ok((
        array32(&input(v, "enc_key")?)?,
        array32(&input(v, "mac_key")?)?,
        iv,
    ))
}

/// `ciphertext || tag` for the plaintext and associated data, which must then
/// decrypt back to the plaintext.
fn check_aead_encrypt(v: &Vector) -> Result<(), String> {
    use tacenta_core::primitives::aead;
    let (enc, mac, iv) = aead_keys(v)?;
    let ad = input(v, "ad")?;
    let plaintext = input(v, "plaintext")?;
    let out = aead::encrypt(&enc, &mac, &iv, &plaintext, &ad);
    eq(&out, &bytes(&v.output)?)?;
    let back = aead::decrypt(&enc, &mac, &iv, &out, &ad)
        .map_err(|_| "refused its own ciphertext".to_string())?;
    eq(&back, &plaintext)
}

/// The receiver: the plaintext, or a refusal. The implementation has one
/// refusal, `DecryptError`, so every invalid vector ends in the same error by
/// construction, which is what the section asks for.
fn check_aead_decrypt(v: &Vector) -> Result<(), String> {
    use tacenta_core::primitives::aead;
    let (enc, mac, iv) = aead_keys(v)?;
    let ad = input(v, "ad")?;
    let received = input(v, "input")?;
    match (
        expects_success(v)?,
        aead::decrypt(&enc, &mac, &iv, &received, &ad),
    ) {
        (true, Ok(plaintext)) => eq(&plaintext, &bytes(&v.output)?),
        (true, Err(_)) => Err("refused an input the vector accepts".to_string()),
        (false, Err(aead::DecryptError)) => Ok(()),
        (false, Ok(_)) => Err("accepted an input the vector refuses".to_string()),
    }
}

/// Build a composite header from a vector's inputs.
///
/// Shared by `composite-header` and `message-encoding`, because a message now
/// carries a composite header and two copies of this would drift.
fn composite_from(v: &Vector) -> Result<tacenta_core::serialization::composite::Composite, String> {
    use tacenta_core::serialization::composite as c;
    let present = input(v, "chunk_present")?;
    let idx = input(v, "chunk_index")?;
    let data = input(v, "chunk_data")?;
    let ag_chunk = if present == [0x01] {
        Some(c::Codeword {
            index: u16::from_be_bytes(idx.as_slice().try_into().map_err(|_| "chunk_index")?),
            data: data.as_slice().try_into().map_err(|_| "chunk_data")?,
        })
    } else {
        None
    };
    let ty = input(v, "ag_type")?;
    let ag_type = match ty.first() {
        Some(0x00) => c::AgreementType::None,
        Some(0x01) => c::AgreementType::Hdr,
        Some(0x02) => c::AgreementType::Ek,
        Some(0x03) => c::AgreementType::EkCt1Ack,
        Some(0x04) => c::AgreementType::Ct1,
        Some(0x05) => c::AgreementType::Ct2,
        _ => return Err("unknown agreement type".to_string()),
    };
    Ok(c::Composite {
        dh: array32(&input(v, "dh")?)?,
        pn: be32(&input(v, "pn")?)?,
        n: be32(&input(v, "n")?)?,
        pq_epoch: be64(&input(v, "pq_epoch")?)?,
        pq_n: be64(&input(v, "pq_n")?)?,
        ag_epoch: be64(&input(v, "ag_epoch")?)?,
        ag_type,
        ag_chunk,
    })
}

/// A byte source that serves a fixed sequence, repeating it, for the one
/// primitive here that consumes randomness. Mirrors the source the crate's
/// own XEdDSA test uses, so the same vector pins the same bytes on both sides.
struct FixedBytes {
    bytes: Vec<u8>,
    at: usize,
}

impl FixedBytes {
    fn new(bytes: Vec<u8>) -> Result<FixedBytes, String> {
        if bytes.is_empty() {
            return Err("nonce must not be empty".to_string());
        }
        Ok(FixedBytes { bytes, at: 0 })
    }
}

impl rand_core::RngCore for FixedBytes {
    fn next_u32(&mut self) -> u32 {
        let mut b = [0u8; 4];
        self.fill_bytes(&mut b);
        u32::from_le_bytes(b)
    }
    fn next_u64(&mut self) -> u64 {
        let mut b = [0u8; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        for d in dest.iter_mut() {
            *d = self.bytes[self.at % self.bytes.len()];
            self.at += 1;
        }
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

// Not random, and says so in the one place it matters: this trait is what
// `xeddsa::sign` asks for, and a fixed sequence satisfies it only for a
// known-answer check.
impl rand_core::CryptoRng for FixedBytes {}

fn input(v: &Vector, key: &str) -> Result<Vec<u8>, String> {
    let s = v.inputs.get(key).ok_or(format!("missing input {key}"))?;
    hex::decode(s).map_err(|e| format!("bad hex for {key}: {e}"))
}

fn bytes(hex_str: &str) -> Result<Vec<u8>, String> {
    hex::decode(hex_str).map_err(|e| format!("bad hex output: {e}"))
}

fn array32(bytes: &[u8]) -> Result<[u8; 32], String> {
    bytes
        .try_into()
        .map_err(|_| "expected 32 bytes".to_string())
}

fn be32(bytes: &[u8]) -> Result<u32, String> {
    let arr: [u8; 4] = bytes
        .try_into()
        .map_err(|_| "expected 4 bytes".to_string())?;
    Ok(u32::from_be_bytes(arr))
}

fn eq(got: &[u8], expected: &[u8]) -> Result<(), String> {
    if got == expected {
        Ok(())
    } else {
        Err(format!(
            "mismatch: got {}, expected {}",
            hex::encode(got),
            hex::encode(expected)
        ))
    }
}

// Double Ratchet protocol vectors. Format: schema/ratchet-vector.schema.json.
// Each vector is a scripted exchange; the runner replays it against
// tacenta-core's ratchet and checks each recorded message key.

/// One ratchet vector file, matching schema/ratchet-vector.schema.json.
#[derive(Deserialize)]
pub struct RatchetFile {
    pub schema_version: u32,
    pub algorithm: String,
    pub source: String,
    pub vectors: Vec<RatchetVector>,
}

#[derive(Deserialize)]
pub struct RatchetVector {
    pub id: String,
    #[serde(default)]
    pub comment: String,
    pub init: RatchetInit,
    pub steps: Vec<RatchetStep>,
}

#[derive(Deserialize)]
pub struct RatchetInit {
    pub sk: String,
    pub alice_pub: String,
    pub bob_pub: String,
    pub dh_ab: String,
}

#[derive(Deserialize)]
pub struct RatchetStep {
    pub actor: String,
    pub op: String,
    #[serde(default = "ok_expect")]
    pub expect: String,
    #[serde(default)]
    pub mk: String,
    /// The expansion of `mk` into the AEAD key, the MAC key and the IV.
    /// Present on model-generated ok steps; optional so that hand-authored
    /// vectors need not carry it.
    #[serde(default)]
    pub message_keys: Option<MessageKeysJson>,
    #[serde(default)]
    pub header: Option<HeaderJson>,
    #[serde(default)]
    pub dh_recv: String,
    #[serde(default)]
    pub dh_send: String,
    #[serde(default)]
    pub new_pub: String,
}

#[derive(Deserialize)]
pub struct HeaderJson {
    pub dh: String,
    pub pn: u32,
    pub n: u32,
}

/// The message-key expansion a step records: what `ratchet::message_keys`
/// must derive from the step's `mk`. Pinning these bytes is what checks the
/// label, the zero salt and the 32/32/16 split order, none of which the
/// ratchet-level `mk` alone exercises.
#[derive(Deserialize)]
pub struct MessageKeysJson {
    pub enc: String,
    pub mac: String,
    pub iv: String,
}

/// Load every `*.json` ratchet vector file in `dir`.
pub fn load_ratchet_dir(dir: &Path) -> Result<Vec<RatchetFile>, String> {
    let mut files = Vec::new();
    let entries = fs::read_dir(dir).map_err(|e| format!("read {}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.extension().and_then(|e| e.to_str()) == Some("json") {
            let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            let file: RatchetFile =
                serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
            files.push(file);
        }
    }
    Ok(files)
}

/// Replay every vector in a file, returning the number of steps checked.
pub fn check_ratchet_file(file: &RatchetFile) -> Result<usize, String> {
    if file.schema_version != 1 {
        return Err(format!(
            "unsupported schema_version {}",
            file.schema_version
        ));
    }
    if file.algorithm != "double-ratchet" {
        return Err(format!("unexpected algorithm {}", file.algorithm));
    }
    let mut checked = 0;
    for v in &file.vectors {
        run_ratchet_vector(v).map_err(|e| format!("[{}] {e}", v.id))?;
        checked += v.steps.len();
    }
    Ok(checked)
}

fn run_ratchet_vector(v: &RatchetVector) -> Result<(), String> {
    let sk = array32(&bytes(&v.init.sk)?)?;
    let alice_pub = array32(&bytes(&v.init.alice_pub)?)?;
    let bob_pub = array32(&bytes(&v.init.bob_pub)?)?;
    let dh_ab = array32(&bytes(&v.init.dh_ab)?)?;

    // The vectors are generated by the model under its own label set; a runner
    // choosing a different one would derive different keys and fail, which is
    // why this is pinned rather than defaulted.
    let mut alice =
        ratchet::init_sender(&sk, alice_pub, bob_pub, &dh_ab, ratchet::LabelSet::Tacenta);
    let mut bob = ratchet::init_receiver(&sk, bob_pub, ratchet::LabelSet::Tacenta);

    for (i, step) in v.steps.iter().enumerate() {
        let state = match step.actor.as_str() {
            "alice" => &mut alice,
            "bob" => &mut bob,
            other => return Err(format!("step {i}: unknown actor {other}")),
        };
        let result: Result<ratchet::Key, ratchet::RatchetError> = match step.op.as_str() {
            "send" => ratchet::send(state).map(|(_header, mk)| mk),
            "receive" => {
                let hj = step
                    .header
                    .as_ref()
                    .ok_or_else(|| format!("step {i}: receive without a header"))?;
                let header = ratchet::Header {
                    dh: array32(&bytes(&hj.dh)?)?,
                    pn: hj.pn,
                    n: hj.n,
                };
                let dh_recv = array32(&bytes(&step.dh_recv)?)?;
                let dh_send = array32(&bytes(&step.dh_send)?)?;
                let new_pub = array32(&bytes(&step.new_pub)?)?;
                ratchet::receive(state, &header, &dh_recv, &dh_send, new_pub)
            }
            other => return Err(format!("step {i}: unknown op {other}")),
        };

        if step.expect == "reject" {
            if result.is_ok() {
                return Err(format!(
                    "step {i} ({} {}): expected rejection, but it succeeded",
                    step.actor, step.op
                ));
            }
        } else {
            let got = result.map_err(|e| format!("step {i} {}: {e:?}", step.op))?;
            let expected = array32(&bytes(&step.mk)?)?;
            if got != expected {
                return Err(format!(
                    "step {i} ({} {}): message key mismatch: got {}, expected {}",
                    step.actor,
                    step.op,
                    hex::encode(got),
                    hex::encode(expected)
                ));
            }
            // The expansion, from the key just checked, under the same label
            // set the vectors were generated with.
            if let Some(mkeys) = &step.message_keys {
                let (enc, mac, iv) = ratchet::message_keys(&got, ratchet::LabelSet::Tacenta);
                let want_enc = array32(&bytes(&mkeys.enc)?)?;
                let want_mac = array32(&bytes(&mkeys.mac)?)?;
                let want_iv = bytes(&mkeys.iv)?;
                if enc != want_enc || mac != want_mac || iv.as_slice() != want_iv.as_slice() {
                    return Err(format!(
                        "step {i} ({} {}): message-key expansion mismatch: got enc {} mac {} iv {}, expected enc {} mac {} iv {}",
                        step.actor,
                        step.op,
                        hex::encode(enc),
                        hex::encode(mac),
                        hex::encode(iv),
                        mkeys.enc,
                        mkeys.mac,
                        mkeys.iv
                    ));
                }
            }
        }
    }
    Ok(())
}

fn ok_expect() -> String {
    "ok".to_string()
}
