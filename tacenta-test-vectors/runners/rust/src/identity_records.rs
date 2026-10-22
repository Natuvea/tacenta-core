//! The identity-record vectors under `vectors/identity/`: the identity pair
//! digest and its verification number (identities-and-devices.md, The
//! identity pair digest), the classification and the lookup, and initiator
//! establishment under an expectation (session-establishment.md, Records,
//! expectations and attribution; Sending the initial message). Layouts:
//! tacenta-test-vectors/README.md, Vector layouts.
//!
//! Every refusal is mapped to the specific `tacenta-core` error it names, not
//! to "any error", and a refusal the pages order before randomness is drawn
//! is checked to draw none.

use tacenta_core::primitives::dh::PublicKeyBytes;
use tacenta_core::sessions::{
    Attribution, ClassifyError, Expectation, Identity, InitiatorError, KeyClass, KeyRefusal,
    LifecycleError, Lookup, PreKeyBundle, PublishedBundle, Record, SessionError, classify,
    establish_initiator, identity_pair_digest, lookup, verification_number,
};

use super::{FixedBytes, Vector, array32, bytes, eq, expects_success, fields_eq, input};

/// The refusal an invalid identity-record vector gives, against the one
/// `tacenta-core` reported: its `refusal`, or any of its `acceptable_refusals`.
fn refused_as(v: &Vector, got: &str) -> Result<(), String> {
    match (v.refusal.as_deref(), v.acceptable_refusals.as_deref()) {
        (Some(want), None) if want == got => Ok(()),
        (Some(want), None) => Err(format!("refused as {got}, where the vector says {want}")),
        (None, Some(allowed)) if allowed.iter().any(|a| a == got) => Ok(()),
        (None, Some(allowed)) => Err(format!(
            "refused as {got}, where the vector allows {}",
            allowed.join(" or ")
        )),
        _ => Err("an invalid identity-record vector names its refusal, one way".to_string()),
    }
}

fn key_refusal_name(refusal: KeyRefusal) -> Result<&'static str, String> {
    match refusal {
        KeyRefusal::NotCanonical => Ok("decode-failure"),
        KeyRefusal::InvalidIdentityKey => Ok("invalid-identity-key"),
        other => Err(format!(
            "unclassified key refusal ({other:?}): name it here and in the schema"
        )),
    }
}

fn key(v: &Vector, name: &str) -> Result<PublicKeyBytes, String> {
    Ok(PublicKeyBytes::from_bytes(array32(&input(v, name)?)?))
}

/// A list of keys, their 32-byte encodings concatenated.
fn keys(data: &[u8]) -> Result<Vec<PublicKeyBytes>, String> {
    let (whole, rest) = data.as_chunks::<32>();
    if !rest.is_empty() {
        return Err(format!(
            "{} bytes is not a whole number of keys",
            data.len()
        ));
    }
    Ok(whole
        .iter()
        .map(|k| PublicKeyBytes::from_bytes(*k))
        .collect())
}

/// A counted list of records: a 4-byte count, then for each record a 4-byte
/// count of current keys, those keys, a 4-byte count of retired keys and
/// those keys. The n-th record is contact n's.
fn records(data: &[u8]) -> Result<Vec<Record>, String> {
    fn take<'a>(data: &'a [u8], at: &mut usize, n: usize) -> Result<&'a [u8], String> {
        let end = at
            .checked_add(n)
            .filter(|end| *end <= data.len())
            .ok_or("the records are truncated")?;
        let out = &data[*at..end];
        *at = end;
        Ok(out)
    }
    fn count(data: &[u8], at: &mut usize) -> Result<usize, String> {
        let b: [u8; 4] = take(data, at, 4)?.try_into().map_err(|_| "a count")?;
        usize::try_from(u32::from_be_bytes(b)).map_err(|_| "a count does not fit".to_string())
    }
    let mut at = 0;
    let n = count(data, &mut at)?;
    let mut out = Vec::new();
    for _ in 0..n {
        let current = count(data, &mut at)?;
        let current = keys(take(data, &mut at, 32 * current)?)?;
        let retired = count(data, &mut at)?;
        let retired = keys(take(data, &mut at, 32 * retired)?)?;
        out.push(Record::new(current, retired));
    }
    if at != data.len() {
        return Err("bytes after the records".to_string());
    }
    Ok(out)
}

fn indices(list: &[usize]) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    for i in list {
        let i = u32::try_from(*i).map_err(|_| "an index does not fit".to_string())?;
        out.extend_from_slice(&i.to_be_bytes());
    }
    Ok(out)
}

/// A lookup's result as the vectors write it: the attribution byte, the
/// contact when there is one, the contacts the key is retired for and the
/// records skipped as malformed.
/// Named values to compare with a vector's `fields`; `None` is a value the
/// vector must leave out.
type Fields = Vec<(&'static str, Option<Vec<u8>>)>;

fn lookup_fields(result: &Lookup) -> Result<Fields, String> {
    let (attribution, contact) = match result.attribution {
        Attribution::Unattributed => (0x00, None),
        Attribution::Contact(c) => (
            0x01,
            Some(
                u32::try_from(c)
                    .map_err(|_| "a contact does not fit")?
                    .to_be_bytes()
                    .to_vec(),
            ),
        ),
        Attribution::Ambiguous => (0x02, None),
        Attribution::RetiredKey => (0x03, None),
    };
    Ok(vec![
        ("attribution", Some(vec![attribution])),
        ("contact", contact),
        ("retired_for", Some(indices(&result.retired_for)?)),
        ("malformed", Some(indices(&result.malformed)?)),
    ])
}

/// The identity pair digest: a valid vector's digest and verification number,
/// the same in either argument order; an invalid vector's refusal.
pub(crate) fn check_pair_digest(v: &Vector) -> Result<(), String> {
    let (k1, k2) = (key(v, "k1")?, key(v, "k2")?);
    let got = identity_pair_digest(&k1, &k2);
    if got.is_ok() && identity_pair_digest(&k2, &k1) != got {
        return Err("the digest depends on the argument order".to_string());
    }
    match (expects_success(v)?, got) {
        (true, Ok(digest)) => fields_eq(
            v,
            &[
                ("digest", Some(digest.to_vec())),
                (
                    "verification_number",
                    Some(verification_number(&digest).to_vec()),
                ),
            ],
        ),
        (true, Err(e)) => Err(format!("refused ({e:?}) a pair the vector admits")),
        (false, Ok(_)) => Err("admitted a pair the vector refuses".to_string()),
        (false, Err(e)) => refused_as(v, key_refusal_name(e)?),
    }
}

/// The verification number of a digest, as 60 ASCII digits.
pub(crate) fn check_verification_number(v: &Vector) -> Result<(), String> {
    if !expects_success(v)? {
        return Err("a verification number is never refused".to_string());
    }
    let digest = array32(&input(v, "digest")?)?;
    eq(&verification_number(&digest), &bytes(&v.output)?)
}

/// A presented key against one record: the class byte, or the refusal.
pub(crate) fn check_identity_classification(v: &Vector) -> Result<(), String> {
    let record = Record::new(keys(&input(v, "current")?)?, keys(&input(v, "retired")?)?);
    match (expects_success(v)?, classify(&key(v, "key")?, &record)) {
        (true, Ok(class)) => {
            let byte = match class {
                KeyClass::Same => 0x01,
                KeyClass::New => 0x02,
                KeyClass::Retired => 0x03,
            };
            eq(&[byte], &bytes(&v.output)?)
        }
        (true, Err(e)) => Err(format!("refused ({e:?}) a classification the vector gives")),
        (false, Ok(class)) => Err(format!("classified as {class:?} a key the vector refuses")),
        (false, Err(ClassifyError::Key(e))) => refused_as(v, key_refusal_name(e)?),
        (false, Err(ClassifyError::MalformedRecord)) => refused_as(v, "malformed-record"),
        (false, Err(other)) => Err(format!(
            "unclassified refusal ({other:?}): name it here and in the schema"
        )),
    }
}

/// A presented key looked up in a party's records: the attribution and what
/// is reported beside it, or the refusal.
pub(crate) fn check_identity_lookup(v: &Vector) -> Result<(), String> {
    let records = records(&input(v, "records")?)?;
    match (expects_success(v)?, lookup(&key(v, "key")?, &records)) {
        (true, Ok(result)) => fields_eq(v, &lookup_fields(&result)?),
        (true, Err(e)) => Err(format!("refused ({e:?}) a lookup the vector gives")),
        (false, Ok(_)) => Err("looked up a key the vector refuses".to_string()),
        (false, Err(e)) => refused_as(v, key_refusal_name(e)?),
    }
}

/// A prekey bundle's fields, read by the layout of message-format.md, Prekey
/// bundle, without the decoder's checks: for `bundle_fields`, a bundle the
/// decoder refuses, which reaches establishment some other way.
fn bundle_from_layout(data: &[u8]) -> Result<PublishedBundle, String> {
    fn take<'a>(data: &'a [u8], at: &mut usize, n: usize) -> Result<&'a [u8], String> {
        let end = at
            .checked_add(n)
            .filter(|end| *end <= data.len())
            .ok_or("the bundle is truncated")?;
        let out = &data[*at..end];
        *at = end;
        Ok(out)
    }
    fn be32(b: &[u8]) -> Result<u32, String> {
        Ok(u32::from_be_bytes(b.try_into().map_err(|_| "4 bytes")?))
    }
    let mut at = 0;
    if take(data, &mut at, 2)? != [0x01, 0x03] {
        return Err("not a version-1 prekey bundle".to_string());
    }
    let identity_key = array32(take(data, &mut at, 32)?)?;
    let signed_prekey = array32(take(data, &mut at, 32)?)?;
    let signed_prekey_signature: [u8; 64] = take(data, &mut at, 64)?
        .try_into()
        .map_err(|_| "64 bytes")?;
    let kem_len = usize::try_from(be32(take(data, &mut at, 4)?)?).map_err(|_| "a length")?;
    let kem_prekey = take(data, &mut at, kem_len)?.to_vec();
    let kem_prekey_signature: [u8; 64] = take(data, &mut at, 64)?
        .try_into()
        .map_err(|_| "64 bytes")?;
    let present = take(data, &mut at, 1)?[0];
    let one_time = array32(take(data, &mut at, 32)?)?;
    let signed_prekey_id = be32(take(data, &mut at, 4)?)?;
    let one_time_prekey_id = be32(take(data, &mut at, 4)?)?;
    let kem_prekey_id = be32(take(data, &mut at, 4)?)?;
    if at != data.len() {
        return Err("bytes after the bundle".to_string());
    }
    let one_time_prekey = match present {
        0x00 => None,
        0x01 => Some(PublicKeyBytes::from_bytes(one_time)),
        other => return Err(format!("presence byte {other:#04x}")),
    };
    Ok(PublishedBundle {
        bundle: PreKeyBundle {
            identity_key: PublicKeyBytes::from_bytes(identity_key),
            signed_prekey: PublicKeyBytes::from_bytes(signed_prekey),
            signed_prekey_signature,
            kem_prekey,
            kem_prekey_signature,
            one_time_prekey,
        },
        signed_prekey_id,
        one_time_prekey_id,
        kem_prekey_id,
    })
}

fn same_bundle(a: &PublishedBundle, b: &PublishedBundle) -> bool {
    a.bundle.identity_key == b.bundle.identity_key
        && a.bundle.signed_prekey == b.bundle.signed_prekey
        && a.bundle.signed_prekey_signature == b.bundle.signed_prekey_signature
        && a.bundle.kem_prekey == b.bundle.kem_prekey
        && a.bundle.kem_prekey_signature == b.bundle.kem_prekey_signature
        && a.bundle.one_time_prekey == b.bundle.one_time_prekey
        && a.signed_prekey_id == b.signed_prekey_id
        && a.one_time_prekey_id == b.one_time_prekey_id
        && a.kem_prekey_id == b.kem_prekey_id
}

/// The bundle a vector offers: `bundle`, which the bundle decoder accepts
/// (and which the layout reading above gives field for field), or
/// `bundle_fields`, which the decoder refuses.
fn offered_bundle(v: &Vector) -> Result<PublishedBundle, String> {
    use tacenta_core::serialization::decode_bundle;
    match (
        v.inputs.contains_key("bundle"),
        v.inputs.contains_key("bundle_fields"),
    ) {
        (true, false) => {
            let encoded = input(v, "bundle")?;
            let wire = decode_bundle(&encoded)
                .map_err(|e| format!("the bundle does not decode: {e:?}"))?;
            let decoded = PublishedBundle {
                bundle: PreKeyBundle {
                    identity_key: PublicKeyBytes::from_bytes(wire.identity_key),
                    signed_prekey: PublicKeyBytes::from_bytes(wire.signed_prekey),
                    signed_prekey_signature: wire.signed_prekey_signature,
                    kem_prekey: wire.kem_prekey,
                    kem_prekey_signature: wire.kem_prekey_signature,
                    one_time_prekey: wire.one_time_prekey.map(PublicKeyBytes::from_bytes),
                },
                signed_prekey_id: wire.signed_prekey_id,
                one_time_prekey_id: wire.one_time_prekey_id,
                kem_prekey_id: wire.kem_prekey_id,
            };
            if !same_bundle(&decoded, &bundle_from_layout(&encoded)?) {
                return Err("the decoder and the layout read the bundle differently".to_string());
            }
            Ok(decoded)
        }
        (false, true) => {
            let encoded = input(v, "bundle_fields")?;
            if decode_bundle(&encoded).is_ok() {
                return Err("bundle_fields is a bundle the decoder accepts".to_string());
            }
            bundle_from_layout(&encoded)
        }
        _ => Err("a vector offers exactly one of bundle and bundle_fields".to_string()),
    }
}

/// The name a vector gives an initiator refusal, and whether the pages place
/// it before anything is drawn. The KEM prekey's input checks may come before
/// or after `EKA` is drawn, and a non-contributory agreement comes after it.
fn initiator_refusal(e: InitiatorError) -> Result<(&'static str, bool), String> {
    Ok(match e {
        InitiatorError::MalformedRecord => ("malformed-record", true),
        InitiatorError::UnexpectedIdentity => ("unexpected-identity", true),
        InitiatorError::RetiredIdentity => ("retired-identity", true),
        InitiatorError::Establish(LifecycleError::InconsistentBundle) => {
            ("inconsistent-bundle", true)
        }
        InitiatorError::Establish(LifecycleError::BadEncoding) => ("non-canonical-key", true),
        InitiatorError::Establish(LifecycleError::Handshake(SessionError::InvalidIdentityKey)) => {
            ("invalid-identity-key", true)
        }
        InitiatorError::Establish(LifecycleError::Handshake(
            SessionError::BadSignedPrekeySignature | SessionError::BadKemPrekeySignature,
        )) => ("authentication-failure", true),
        InitiatorError::Establish(LifecycleError::Kem) => ("kem-input", false),
        InitiatorError::Establish(LifecycleError::Handshake(
            SessionError::NonContributoryAgreement,
        )) => ("non-contributory", false),
        other => {
            return Err(format!(
                "unclassified refusal ({other:?}): name it here and in the schema"
            ));
        }
    })
}

/// Initiator establishment under an expectation: an admitted bundle gives a
/// session whose peer key is the bundle's, attributed by a lookup in all the
/// records; a refused one gives the refusal the vector names, and, where the
/// pages place it before randomness, draws nothing.
pub(crate) fn check_initiator_expectation(v: &Vector) -> Result<(), String> {
    let records = records(&input(v, "records")?)?;
    let expectation = match input(v, "expectation")?.as_slice() {
        [0x00] => Expectation::first_contact(&records),
        [0x01, index @ ..] => {
            let index: [u8; 4] = index
                .try_into()
                .map_err(|_| "a known expectation names a 4-byte contact")?;
            let index = usize::try_from(u32::from_be_bytes(index)).map_err(|_| "an index")?;
            Expectation::known(
                records
                    .get(index)
                    .ok_or("a known expectation names no record")?,
            )
        }
        _ => return Err("not an expectation".to_string()),
    };
    let bundle = offered_bundle(v)?;
    let initiator = Identity::from_secret(array32(&input(v, "initiator_identity_secret")?)?);
    let mut rng = FixedBytes::new(vec![0x5c; 64])?;
    let outcome = establish_initiator(&initiator, &bundle, &expectation, &mut rng);
    match (expects_success(v)?, outcome) {
        (true, Ok(session)) => {
            let peer = session.peer_identity();
            let attributed = lookup(&peer, &records)
                .map_err(|e| format!("the session's peer key is refused by the lookup ({e:?})"))?;
            let mut got = vec![("peer_identity", Some(peer.as_bytes().to_vec()))];
            got.extend(lookup_fields(&attributed)?);
            fields_eq(v, &got)
        }
        (true, Err(e)) => Err(format!("refused ({e:?}) a bundle the vector admits")),
        (false, Ok(_)) => Err("established from a bundle the vector refuses".to_string()),
        (false, Err(e)) => {
            let (name, before_randomness) = initiator_refusal(e)?;
            if before_randomness && rng.drawn() != 0 {
                return Err(format!(
                    "refused as {name} after drawing {} random bytes",
                    rng.drawn()
                ));
            }
            refused_as(v, name)
        }
    }
}
