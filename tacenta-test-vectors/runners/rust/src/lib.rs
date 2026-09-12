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
    /// Which refusal an invalid persisted-state vector names: for stored
    /// bytes, the one the reader gives (session-persistence.md, Rejection),
    /// `wrong-version` or `short-or-malformed`; for operations whose last step
    /// is refused, `counter-exhaustion` (ratchet.md, Sending and receiving;
    /// sparse-pq-ratchet.md, Sending and Receiving).
    #[serde(default)]
    pub refusal: Option<String>,
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

/// A vector file's `algorithm`, read before the file is parsed as either shape.
///
/// `vectors/malformed-input/` holds both: a Double Ratchet scenario file and
/// known-answer decoder files. Each loader takes its own shape from a directory
/// and leaves the other to its loader, and a file with no `algorithm` is an
/// error in both rather than a file neither loads.
fn algorithm_of(text: &str, path: &Path) -> Result<String, String> {
    let value: serde_json::Value =
        serde_json::from_str(text).map_err(|e| format!("{}: {e}", path.display()))?;
    value
        .get("algorithm")
        .and_then(|a| a.as_str())
        .map(str::to_string)
        .ok_or_else(|| format!("{}: no algorithm", path.display()))
}

/// The one scenario algorithm; every other file is a known-answer file.
const SCENARIO_ALGORITHM: &str = "double-ratchet";

/// Load every known-answer `*.json` vector file in `dir`, leaving any scenario
/// file to `load_ratchet_dir`.
pub fn load_dir(dir: &Path) -> Result<Vec<VectorFile>, String> {
    let mut files = Vec::new();
    let entries = fs::read_dir(dir).map_err(|e| format!("read {}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.extension().and_then(|e| e.to_str()) == Some("json") {
            let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            if algorithm_of(&text, &path)? == SCENARIO_ALGORITHM {
                continue;
            }
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
        // The decoders' verdicts on whole encodings, a curve key re-spelled in
        // each position among them (message-format.md, Curve public keys): an
        // accepted encoding re-encodes to `output`, and a refused one is refused.
        "composite-header-decode" => {
            use tacenta_core::serialization::composite as c;
            let encoding = input(v, "encoding")?;
            decoder_verdict(v, c::decode_composite(&encoding), |(h, rest)| {
                [c::encode_composite(&h).as_slice(), rest].concat()
            })
        }
        "prekey-bundle-decode" => {
            use tacenta_core::serialization;
            let encoding = input(v, "encoding")?;
            decoder_verdict(v, serialization::decode_bundle(&encoding), |b| {
                serialization::encode_bundle(&b)
            })
        }
        "initial-message-decode" => {
            use tacenta_core::serialization;
            let encoding = input(v, "encoding")?;
            decoder_verdict(v, serialization::decode_initial(&encoding), |d| {
                serialization::encode_initial(
                    &d.identity,
                    &d.ephemeral,
                    &d.kem_ciphertext,
                    d.signed_prekey_id,
                    d.one_time_prekey_id,
                    d.kem_prekey_id,
                    &d.message,
                )
            })
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
        // The two ratchets' persisted states, their readers' semantic rules
        // and the refusal each reader gives (session-persistence.md, Ratchet
        // state, Sparse ratchet state, Semantic rules of the leaf formats).
        "ratchet-state" => check_ratchet_state(v),
        "sparse-ratchet-state" => check_sparse_ratchet_state(v),
        // The Triple Ratchet's state, which composes the two above, and the
        // ML-KEM Braid's (session-persistence.md, Triple ratchet state;
        // Braid; Semantic rules of the leaf formats).
        "triple-ratchet-state" => check_triple_ratchet_state(v),
        "braid-state" => check_braid_state(v),
        // The bounded protobuf profile's two readers (protobuf-profile.md).
        "protobuf-ratchet-body" => check_ratchet_body(v),
        "protobuf-prekey-envelope" => check_prekey_envelope(v),
        // The AEAD (message-format.md, Authenticated encryption).
        "aead-encrypt" => check_aead_encrypt(v),
        "aead-decrypt" => check_aead_decrypt(v),
        other => Err(format!("no runner for algorithm {other}")),
    }
}

/// A decoder's answer against a vector's `result`: a valid vector's input is
/// accepted and what it decodes to re-encodes to `output`, and an invalid
/// vector's input is refused, whichever refusal the implementation reports.
fn decoder_verdict<T, E: std::fmt::Debug>(
    v: &Vector,
    decoded: Result<T, E>,
    reencode: impl FnOnce(T) -> Vec<u8>,
) -> Result<(), String> {
    match (expects_success(v)?, decoded) {
        (true, Ok(value)) => eq(&reencode(value), &bytes(&v.output)?),
        (true, Err(e)) => Err(format!("refused an encoding the model accepts: {e:?}")),
        (false, Ok(_)) => Err("accepted an encoding the model refuses".to_string()),
        (false, Err(_)) => Ok(()),
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
    let (codewords, _rest) = bytes.as_chunks::<{ 2 + CHUNK_BYTES }>();
    codewords
        .iter()
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

/// The refusal an invalid persisted-state vector names, against the one the
/// reader gave.
fn refusal_is(v: &Vector, got: &str) -> Result<(), String> {
    match v.refusal.as_deref() {
        Some(want) if want == got => Ok(()),
        Some(want) => Err(format!("refused as {got}, where the vector says {want}")),
        None => Err("an invalid persisted-state vector names its refusal".to_string()),
    }
}

/// A vector's `fields` value by name, as bytes, or `None` when the vector
/// leaves the field out.
fn field(v: &Vector, name: &str) -> Result<Option<Vec<u8>>, String> {
    let fields = v
        .fields
        .as_ref()
        .ok_or("a valid stored-state vector carries fields")?;
    fields
        .get(name)
        .map(|h| hex::decode(h).map_err(|e| format!("bad hex for field {name}: {e}")))
        .transpose()
}

fn required_field(v: &Vector, name: &str) -> Result<Vec<u8>, String> {
    field(v, name)?.ok_or_else(|| format!("the vector has no field {name}"))
}

/// The names a vector's `fields` may use, and no others.
fn fields_named(v: &Vector, names: &[&str]) -> Result<(), String> {
    let fields = v
        .fields
        .as_ref()
        .ok_or("a valid stored-state vector carries fields")?;
    match fields.keys().find(|k| !names.contains(&k.as_str())) {
        Some(extra) => Err(format!(
            "the vector names {extra}, which the format has not"
        )),
        None => Ok(()),
    }
}

/// A 32-byte key with the format's presence byte in front: `0x01` and the
/// key, or `0x00` and 32 zero bytes when the vector leaves it out.
fn optional_key(v: &Vector, name: &str) -> Result<Vec<u8>, String> {
    Ok(match field(v, name)? {
        Some(k) if k.len() == 32 => [&[0x01][..], &k].concat(),
        Some(k) => return Err(format!("field {name}: expected 32 bytes, got {}", k.len())),
        None => [0u8; 33].to_vec(),
    })
}

/// A run of entries of `width` bytes, and their count as four big-endian
/// bytes.
fn counted(entries: &[u8], width: usize) -> Result<[u8; 4], String> {
    if !entries.len().is_multiple_of(width) {
        return Err(format!(
            "{} bytes is not a whole number of {width}-byte entries",
            entries.len()
        ));
    }
    u32::try_from(entries.len() / width)
        .map(u32::to_be_bytes)
        .map_err(|_| "too many entries".to_string())
}

/// Where a vector's steps, replayed, ended: every step taken, or the step at
/// `index` refused, with the name a vector gives the refusal and whether it
/// was the last step.
enum Replayed {
    Taken,
    Refused {
        index: usize,
        last: bool,
        refusal: String,
    },
}

/// A replay against the vector's `result`: a valid vector's steps are all
/// taken, and an invalid vector's are taken up to the last, which is refused
/// with the refusal the vector names. `Ok(true)` when the state reached is to
/// be written and checked; an invalid vector reaches no state to check.
fn replay_verdict(v: &Vector, replayed: Replayed) -> Result<bool, String> {
    match (expects_success(v)?, replayed) {
        (true, Replayed::Taken) => Ok(true),
        (true, Replayed::Refused { index, refusal, .. }) => {
            Err(format!("step {index}: refused ({refusal})"))
        }
        (false, Replayed::Taken) => {
            Err("every step was taken, where the vector says the last is refused".to_string())
        }
        (
            false,
            Replayed::Refused {
                index,
                last: false,
                refusal,
            },
        ) => Err(format!(
            "step {index}: refused ({refusal}) before the last step"
        )),
        (false, Replayed::Refused { refusal, .. }) => refusal_is(v, &refusal).map(|()| false),
    }
}

/// The name a vector gives a refused operation of the classical ratchet:
/// `ChainExhausted` is `counter-exhaustion`. No vector names any other, so
/// any other is reported as the error.
fn ratchet_refusal(e: &tacenta_core::ratchet::RatchetError) -> String {
    match e {
        tacenta_core::ratchet::RatchetError::ChainExhausted => "counter-exhaustion".to_string(),
        other => format!("{other:?}"),
    }
}

/// A ratchet-state vector's steps, replayed on `state`: `0x00` is a send,
/// and `0x01` a receive followed by the header's `dh(32) || pn(4) || n(4)`
/// and the step's `dh_recv(32) || dh_send(32) || new_pub(32)`. The replay
/// stops at the first step the crate refuses.
fn replay_ratchet_steps(
    state: &mut tacenta_core::ratchet::State,
    steps: &[u8],
) -> Result<Replayed, String> {
    use tacenta_core::ratchet;
    let mut at = 0;
    let mut i = 0;
    while at < steps.len() {
        let taken = match steps[at] {
            0x00 => {
                at += 1;
                ratchet::send(state).map(|_| ())
            }
            0x01 => {
                let r = steps
                    .get(at + 1..at + 137)
                    .ok_or_else(|| format!("step {i}: a receive step cut short"))?;
                let header = ratchet::Header {
                    dh: array32(&r[0..32])?,
                    pn: be32(&r[32..36])?,
                    n: be32(&r[36..40])?,
                };
                at += 137;
                ratchet::receive(
                    state,
                    &header,
                    &array32(&r[40..72])?,
                    &array32(&r[72..104])?,
                    array32(&r[104..136])?,
                )
                .map(|_| ())
            }
            other => return Err(format!("step {i}: unknown operation {other:#04x}")),
        };
        if let Err(e) = taken {
            return Ok(Replayed::Refused {
                index: i,
                last: at == steps.len(),
                refusal: ratchet_refusal(&e),
            });
        }
        i += 1;
    }
    Ok(Replayed::Taken)
}

/// A classical ratchet state's stored bytes. Either built by operations --
/// from `role` (`00` the initiator, `init_sender`, with `sk`, `our_pub`,
/// `peer_pub` and `dh_out`; `01` the responder, `init_receiver`, with `sk` and
/// `our_pub`) or from `start`, stored bytes the reader accepts, then `steps`
/// -- and then written, which must give `output`, and read back and written
/// again, which must give it too; or, for an invalid vector, with the last
/// step refused with its `refusal`. Or offered as `bytes` to the reader, which
/// accepts them with `fields` or refuses them with `refusal`.
fn check_ratchet_state(v: &Vector) -> Result<(), String> {
    use tacenta_core::ratchet::{self, RatchetDecodeError, State};
    if v.inputs.contains_key("bytes") {
        let stored = input(v, "bytes")?;
        return match (expects_success(v)?, State::from_bytes(&stored)) {
            (true, Ok(state)) => {
                eq(&state.to_bytes(), &stored)?;
                ratchet_fields_agree(v, &state, &stored)
            }
            (true, Err(e)) => Err(format!("refused ({e:?}) stored bytes the vector accepts")),
            (false, Ok(_)) => Err("accepted stored bytes the vector refuses".to_string()),
            (false, Err(e)) => refusal_is(
                v,
                match e {
                    RatchetDecodeError::UnknownVersion => "wrong-version",
                    RatchetDecodeError::TooShort | RatchetDecodeError::Malformed => {
                        "short-or-malformed"
                    }
                },
            ),
        };
    }
    let mut state = if v.inputs.contains_key("start") {
        State::from_bytes(&input(v, "start")?)
            .map_err(|e| format!("refused ({e:?}) the start state the vector gives"))?
    } else {
        let sk = array32(&input(v, "sk")?)?;
        let our_pub = array32(&input(v, "our_pub")?)?;
        match input(v, "role")?.as_slice() {
            [0x00] => ratchet::init_sender(
                &sk,
                our_pub,
                array32(&input(v, "peer_pub")?)?,
                &array32(&input(v, "dh_out")?)?,
                ratchet::LabelSet::Tacenta,
            ),
            [0x01] => ratchet::init_receiver(&sk, our_pub, ratchet::LabelSet::Tacenta),
            other => return Err(format!("unknown role {}", hex::encode(other))),
        }
    };
    if !replay_verdict(v, replay_ratchet_steps(&mut state, &input(v, "steps")?)?)? {
        return Ok(());
    }
    let stored = state.to_bytes();
    eq(&stored, &bytes(&v.output)?)?;
    let back = State::from_bytes(&stored)
        .map_err(|e| format!("the reader refuses ({e:?}) what the writer wrote"))?;
    eq(&back.to_bytes(), &stored)
}

/// An accepted ratchet state against the vector's `fields`: the fields laid
/// out as the format lays them out are the stored bytes, and what the state's
/// accessors show agrees with them.
fn ratchet_fields_agree(
    v: &Vector,
    state: &tacenta_core::ratchet::State,
    stored: &[u8],
) -> Result<(), String> {
    fields_named(
        v,
        &[
            "dhs_pub", "dhr_pub", "rk", "cks", "ckr", "ns", "nr", "pn", "events", "labels",
            "skipped",
        ],
    )?;
    let skipped = required_field(v, "skipped")?;
    let laid_out = [
        &[0x01][..],
        &required_field(v, "dhs_pub")?,
        &optional_key(v, "dhr_pub")?,
        &required_field(v, "rk")?,
        &optional_key(v, "cks")?,
        &optional_key(v, "ckr")?,
        &required_field(v, "ns")?,
        &required_field(v, "nr")?,
        &required_field(v, "pn")?,
        &required_field(v, "events")?,
        &required_field(v, "labels")?,
        &counted(&skipped, 72)?,
        &skipped,
    ]
    .concat();
    eq(&laid_out, stored).map_err(|e| format!("fields laid out: {e}"))?;
    eq(&state.sending_public(), &required_field(v, "dhs_pub")?)?;
    eq(&state.send_count().to_be_bytes(), &required_field(v, "ns")?)?;
    eq(
        &state.receive_count().to_be_bytes(),
        &required_field(v, "nr")?,
    )?;
    if state.skipped_len() != skipped.len() / 72 {
        return Err(format!(
            "holds {} stored keys, the vector {}",
            state.skipped_len(),
            skipped.len() / 72
        ));
    }
    let shape = match (field(v, "cks")?.is_some(), field(v, "ckr")?.is_some()) {
        (true, false) => Some(true),
        (false, false) => Some(false),
        _ => None,
    };
    if state.started_as_sender() != shape {
        return Err("the chains present differ from the vector's".to_string());
    }
    Ok(())
}

/// A sparse-ratchet-state vector's steps, replayed on `state`. Each is
/// `op(1) || epoch(8) || output_present(1) || output_epoch(8) ||
/// output_key(32)`, the output zeroed when absent, and a receive (`op` `01`)
/// is followed by the message number `n(8)`; a send's `op` is `00`. The replay
/// stops at the first step the crate refuses, and `ChainExhausted` is named
/// `counter-exhaustion`, as for the classical ratchet.
fn replay_sparse_steps(state: &mut tacenta_spqr::State, steps: &[u8]) -> Result<Replayed, String> {
    use tacenta_spqr::{Output, SpqrError};
    let mut at = 0;
    let mut i = 0;
    while at < steps.len() {
        let r = steps
            .get(at..at + 50)
            .ok_or_else(|| format!("step {i}: cut short"))?;
        let epoch = be64(&r[1..9])?;
        let out = match r[9] {
            0x00 => None,
            0x01 => Some(Output::new(be64(&r[10..18])?, array32(&r[18..50])?)),
            other => return Err(format!("step {i}: output presence {other:#04x}")),
        };
        let taken = match r[0] {
            0x00 => {
                at += 50;
                state.send(epoch, out.as_ref()).map(|_| ())
            }
            0x01 => {
                let n = be64(
                    steps
                        .get(at + 50..at + 58)
                        .ok_or_else(|| format!("step {i}: a receive step cut short"))?,
                )?;
                at += 58;
                state.receive(epoch, out.as_ref(), n).map(|_| ())
            }
            other => return Err(format!("step {i}: unknown operation {other:#04x}")),
        };
        if let Err(e) = taken {
            return Ok(Replayed::Refused {
                index: i,
                last: at == steps.len(),
                refusal: match e {
                    SpqrError::ChainExhausted => "counter-exhaustion".to_string(),
                    other => format!("{other:?}"),
                },
            });
        }
        i += 1;
    }
    Ok(Replayed::Taken)
}

/// A sparse ratchet state's stored bytes, the same two ways as
/// `check_ratchet_state`: built from `direction` (`00` `A2b`, `01` `B2a`) and
/// `sk`, or from `start`, then `steps`; or offered as `bytes`.
fn check_sparse_ratchet_state(v: &Vector) -> Result<(), String> {
    use tacenta_spqr::{Direction, SpqrDecodeError, State};
    if v.inputs.contains_key("bytes") {
        let stored = input(v, "bytes")?;
        return match (expects_success(v)?, State::from_bytes(&stored)) {
            (true, Ok(state)) => {
                eq(&state.to_bytes(), &stored)?;
                sparse_fields_agree(v, &state, &stored)
            }
            (true, Err(e)) => Err(format!("refused ({e:?}) stored bytes the vector accepts")),
            (false, Ok(_)) => Err("accepted stored bytes the vector refuses".to_string()),
            (false, Err(e)) => refusal_is(
                v,
                match e {
                    SpqrDecodeError::UnknownVersion => "wrong-version",
                    SpqrDecodeError::TooShort | SpqrDecodeError::Malformed => "short-or-malformed",
                },
            ),
        };
    }
    let mut state = if v.inputs.contains_key("start") {
        State::from_bytes(&input(v, "start")?)
            .map_err(|e| format!("refused ({e:?}) the start state the vector gives"))?
    } else {
        let sk = input(v, "sk")?;
        match input(v, "direction")?.as_slice() {
            [0x00] => State::init(&sk, Direction::A2b),
            [0x01] => State::init(&sk, Direction::B2a),
            other => return Err(format!("unknown direction {}", hex::encode(other))),
        }
    };
    if !replay_verdict(v, replay_sparse_steps(&mut state, &input(v, "steps")?)?)? {
        return Ok(());
    }
    let stored = state.to_bytes();
    eq(&stored, &bytes(&v.output)?)?;
    let back = State::from_bytes(&stored)
        .map_err(|e| format!("the reader refuses ({e:?}) what the writer wrote"))?;
    eq(&back.to_bytes(), &stored)
}

/// An accepted sparse ratchet state against the vector's `fields`, as
/// `ratchet_fields_agree` does for the classical one.
fn sparse_fields_agree(
    v: &Vector,
    state: &tacenta_spqr::State,
    stored: &[u8],
) -> Result<(), String> {
    use tacenta_spqr::Direction;
    fields_named(v, &["rk", "epoch", "direction", "chains", "skipped"])?;
    let chains = required_field(v, "chains")?;
    let skipped = required_field(v, "skipped")?;
    let laid_out = [
        &[0x01][..],
        &required_field(v, "rk")?,
        &required_field(v, "epoch")?,
        &required_field(v, "direction")?,
        &counted(&chains, 90)?,
        &chains,
        &counted(&skipped, 48)?,
        &skipped,
    ]
    .concat();
    eq(&laid_out, stored).map_err(|e| format!("fields laid out: {e}"))?;
    eq(&state.epoch().to_be_bytes(), &required_field(v, "epoch")?)?;
    let direction = match state.direction() {
        Direction::A2b => 0x00,
        Direction::B2a => 0x01,
    };
    eq(&[direction], &required_field(v, "direction")?)?;
    if state.skipped_len() != skipped.len() / 48 {
        return Err(format!(
            "holds {} stored keys, the vector {}",
            state.skipped_len(),
            skipped.len() / 48
        ));
    }
    for entry in chains.chunks(90) {
        let epoch = be64(&entry[0..8])?;
        let receive = &entry[49..90];
        let want = (receive[0] == 0x01)
            .then(|| be64(&receive[33..41]))
            .transpose()?;
        if state.receive_count(epoch) != want {
            return Err(format!(
                "epoch {epoch}'s receiving chain differs from the vector's"
            ));
        }
    }
    Ok(())
}

/// An agreement output as the persisted-state steps write one:
/// `output_present(1) || output_epoch(8) || output_key(32)`, zeroed when
/// absent.
fn step_output(r: &[u8]) -> Result<Option<tacenta_triple::Output>, String> {
    match r[0] {
        0x00 => Ok(None),
        0x01 => Ok(Some(tacenta_triple::Output::new(
            be64(&r[1..9])?,
            array32(&r[9..41])?,
        ))),
        other => Err(format!("output presence {other:#04x}")),
    }
}

/// A triple-ratchet-state vector's steps, replayed on `state`. `00` is a send,
/// followed by `sending_epoch(8)` and the agreement's output; `01` is a
/// receive, followed by the classical header's `dh(32) || pn(4) || n(4)`, the
/// step's `dh_recv(32) || dh_send(32) || new_pub(32)`, the sparse half's
/// `epoch(8) || pq_n(8)`, and the output. A receive returns a candidate state
/// the caller commits, so this commits it, which is what the session layer
/// does once the message has authenticated.
fn replay_triple_steps(
    state: &mut tacenta_triple::State,
    steps: &[u8],
) -> Result<Replayed, String> {
    use tacenta_triple::{DrHeader, Header};
    let mut at = 0;
    let mut i = 0;
    while at < steps.len() {
        let taken = match steps[at] {
            0x00 => {
                let r = steps
                    .get(at + 1..at + 50)
                    .ok_or_else(|| format!("step {i}: a send step cut short"))?;
                let epoch = be64(&r[0..8])?;
                let out = step_output(&r[8..49])?;
                at += 50;
                state.send(epoch, out.as_ref()).map(|_| ())
            }
            0x01 => {
                let r = steps
                    .get(at + 1..at + 194)
                    .ok_or_else(|| format!("step {i}: a receive step cut short"))?;
                let header = Header {
                    dr: DrHeader {
                        dh: array32(&r[0..32])?,
                        pn: be32(&r[32..36])?,
                        n: be32(&r[36..40])?,
                    },
                    epoch: be64(&r[136..144])?,
                    pq_n: be64(&r[144..152])?,
                };
                let out = step_output(&r[152..193])?;
                let dh_recv = array32(&r[40..72])?;
                let dh_send = array32(&r[72..104])?;
                let new_pub = array32(&r[104..136])?;
                at += 194;
                match state.receive(&header, &dh_recv, &dh_send, new_pub, out.as_ref()) {
                    Ok((next, _key)) => {
                        state.commit(next);
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            }
            other => return Err(format!("step {i}: unknown operation {other:#04x}")),
        };
        if let Err(e) = taken {
            return Ok(Replayed::Refused {
                index: i,
                last: at == steps.len(),
                // No vector names a refused Triple Ratchet operation, so any
                // refusal is reported as the error it was rather than mapped.
                refusal: format!("{e:?}"),
            });
        }
        i += 1;
    }
    Ok(Replayed::Taken)
}

/// A Triple Ratchet state's stored bytes, the same two ways as
/// `check_ratchet_state`: built from `role` and the initialisation parameters,
/// or from `start`, then `steps`; or offered as `bytes` to the reader.
fn check_triple_ratchet_state(v: &Vector) -> Result<(), String> {
    use tacenta_triple::{LabelSet, State, TripleDecodeError};
    if v.inputs.contains_key("bytes") {
        let stored = input(v, "bytes")?;
        return match (expects_success(v)?, State::from_bytes(&stored)) {
            (true, Ok(state)) => {
                eq(&state.to_bytes(), &stored)?;
                triple_fields_agree(v, &stored)
            }
            (true, Err(e)) => Err(format!("refused ({e:?}) stored bytes the vector accepts")),
            (false, Ok(_)) => Err("accepted stored bytes the vector refuses".to_string()),
            (false, Err(e)) => refusal_is(
                v,
                match e {
                    TripleDecodeError::UnknownVersion => "wrong-version",
                    TripleDecodeError::TooShort | TripleDecodeError::Malformed => {
                        "short-or-malformed"
                    }
                },
            ),
        };
    }
    let mut state = if v.inputs.contains_key("start") {
        State::from_bytes(&input(v, "start")?)
            .map_err(|e| format!("refused ({e:?}) the start state the vector gives"))?
    } else {
        let sk = input(v, "sk")?;
        let our_pub = array32(&input(v, "our_pub")?)?;
        match input(v, "role")?.as_slice() {
            [0x00] => State::init_sender(
                &sk,
                our_pub,
                array32(&input(v, "peer_pub")?)?,
                &array32(&input(v, "dh_out")?)?,
                LabelSet::Tacenta,
            ),
            [0x01] => State::init_receiver(&sk, our_pub, LabelSet::Tacenta),
            other => return Err(format!("unknown role {}", hex::encode(other))),
        }
    };
    if !replay_verdict(v, replay_triple_steps(&mut state, &input(v, "steps")?)?)? {
        return Ok(());
    }
    let stored = state.to_bytes();
    eq(&stored, &bytes(&v.output)?)?;
    let back = State::from_bytes(&stored)
        .map_err(|e| format!("the reader refuses ({e:?}) what the writer wrote"))?;
    eq(&back.to_bytes(), &stored)
}

/// An accepted Triple Ratchet state against the vector's `fields`: the two
/// halves, each length-prefixed, laid out as the page lays them out are the
/// stored bytes, and each half is one its own reader accepts. That last part
/// is what leaves the composition's own rule as the only thing this format
/// adds.
fn triple_fields_agree(v: &Vector, stored: &[u8]) -> Result<(), String> {
    fields_named(v, &["classical", "post_quantum"])?;
    let classical = required_field(v, "classical")?;
    let post_quantum = required_field(v, "post_quantum")?;
    let laid_out = [
        &[0x01][..],
        &u32::try_from(classical.len())
            .map_err(|_| "the classical half is too long".to_string())?
            .to_be_bytes(),
        &classical,
        &u32::try_from(post_quantum.len())
            .map_err(|_| "the post_quantum half is too long".to_string())?
            .to_be_bytes(),
        &post_quantum,
    ]
    .concat();
    eq(&laid_out, stored).map_err(|e| format!("fields laid out: {e}"))?;
    tacenta_core::ratchet::State::from_bytes(&classical)
        .map(|_| ())
        .map_err(|e| format!("the classical half is refused by its own reader: {e:?}"))?;
    tacenta_spqr::State::from_bytes(&post_quantum)
        .map(|_| ())
        .map_err(|e| format!("the post_quantum half is refused by its own reader: {e:?}"))
}

/// One received Braid message, as the vectors write it: `epoch(8) ||
/// type(1) || chunk_present(1) || chunk_index(2) || chunk(32)`, the type
/// byte being `AgreementType`'s (CONSTANTS.md).
fn braid_message(r: &[u8]) -> Result<tacenta_braid::Msg, String> {
    use tacenta_braid::{Msg, MsgType};
    let ty = match r[8] {
        0x00 => MsgType::None,
        0x01 => MsgType::Hdr,
        0x02 => MsgType::Ek,
        0x03 => MsgType::EkCt1Ack,
        0x04 => MsgType::Ct1,
        0x05 => MsgType::Ct2,
        other => return Err(format!("unknown agreement type {other:#04x}")),
    };
    let data = match r[9] {
        0x00 => None,
        0x01 => Some(tacenta_erasure::Chunk {
            index: u16::from_be_bytes([r[10], r[11]]),
            data: r[12..44]
                .try_into()
                .map_err(|_| "codeword data".to_string())?,
        }),
        other => return Err(format!("chunk presence {other:#04x}")),
    };
    Ok(Msg {
        epoch: be64(&r[0..8])?,
        ty,
        data,
    })
}

/// A Braid's stored bytes. Either offered as `bytes` to the reader, which
/// accepts them with `fields` or refuses them with `refusal`; or a `start`
/// the reader accepts followed by `steps`, each a received message, whose
/// result is written as `output` and read back.
///
/// Only the two transitions out of `Ct2Sampled` are driven this way. Every
/// other transition needs a key pair or an encapsulation state, whose layout
/// `session-persistence.md` delegates and the model therefore does not build
/// (`Model.PersistedState`, BraidState).
fn check_braid_state(v: &Vector) -> Result<(), String> {
    use tacenta_braid::Braid;
    if v.inputs.contains_key("bytes") {
        let stored = input(v, "bytes")?;
        return match (expects_success(v)?, Braid::from_bytes(&stored)) {
            (true, Ok(b)) => {
                eq(&b.to_bytes(), &stored)?;
                braid_fields_agree(v, &b, &stored)
            }
            (true, Err(e)) => Err(format!("refused ({e:?}) stored bytes the vector accepts")),
            (false, Ok(_)) => Err("accepted stored bytes the vector refuses".to_string()),
            (false, Err(e)) => refusal_is(
                v,
                match e {
                    tacenta_braid::BraidDecodeError::UnknownVersion => "wrong-version",
                    tacenta_braid::BraidDecodeError::TooShort
                    | tacenta_braid::BraidDecodeError::Malformed => "short-or-malformed",
                },
            ),
        };
    }
    let mut braid = Braid::from_bytes(&input(v, "start")?)
        .map_err(|e| format!("refused ({e:?}) the start state the vector gives"))?;
    let steps = input(v, "steps")?;
    if !steps.len().is_multiple_of(44) {
        return Err(format!(
            "steps: {} bytes is not a whole number of messages",
            steps.len()
        ));
    }
    for (i, r) in steps.chunks(44).enumerate() {
        let msg = braid_message(r).map_err(|e| format!("step {i}: {e}"))?;
        let (_epoch, _out, next) = braid.receive(&msg);
        braid.commit(next);
    }
    let stored = braid.to_bytes();
    eq(&stored, &bytes(&v.output)?)?;
    let back = Braid::from_bytes(&stored)
        .map_err(|e| format!("the reader refuses ({e:?}) what the writer wrote"))?;
    eq(&back.to_bytes(), &stored)
}

/// An accepted Braid against the vector's `fields`: the tag, and for every
/// live state the epoch, the authenticator and the tag's length-prefixed
/// fields, laid out as the page lays them out. `Failed` carries only its tag.
fn braid_fields_agree(
    v: &Vector,
    braid: &tacenta_braid::Braid,
    stored: &[u8],
) -> Result<(), String> {
    fields_named(v, &["state_tag", "epoch", "auth", "fields"])?;
    let tag = required_field(v, "state_tag")?;
    let failed = tag == [11u8];
    let laid_out = if failed {
        [&[0x01][..], &tag].concat()
    } else {
        [
            &[0x01][..],
            &tag,
            &required_field(v, "epoch")?,
            &required_field(v, "auth")?,
            &required_field(v, "fields")?,
        ]
        .concat()
    };
    eq(&laid_out, stored).map_err(|e| format!("fields laid out: {e}"))?;
    eq(&[braid.state_tag()], &tag)?;
    if failed {
        if !braid.failed() {
            return Err("the vector's tag is Failed and the Braid is not".to_string());
        }
    } else {
        if braid.failed() {
            return Err("the Braid has failed and the vector's tag is a live state".to_string());
        }
        eq(&braid.epoch().to_be_bytes(), &required_field(v, "epoch")?)?;
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

/// Load every `*.json` ratchet scenario file in `dir`, leaving any known-answer
/// file to `load_dir`.
pub fn load_ratchet_dir(dir: &Path) -> Result<Vec<RatchetFile>, String> {
    let mut files = Vec::new();
    let entries = fs::read_dir(dir).map_err(|e| format!("read {}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.extension().and_then(|e| e.to_str()) == Some("json") {
            let text = fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            if algorithm_of(&text, &path)? != SCENARIO_ALGORITHM {
                continue;
            }
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
