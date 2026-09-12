//! sessions::lifecycle: identity, prekeys, and the establish-and-message flow.
//!
//! This ties the PQXDH handshake (this module's parent), the Double Ratchet, and
//! the wire format into the flow a consumer actually uses: create an identity,
//! publish prekeys, establish a session from a bundle or from an incoming initial
//! message, then encrypt and decrypt. It is orchestration, not verified-zone
//! code: it drives the RNG and the trusted primitives, while the ratchet leaf it
//! calls stays pure.
//!
//! The Diffie-Hellman boundary is threaded here. The ratchet takes DH outputs as
//! bytes, so on each receive this layer computes the agreement, generates a fresh
//! ratchet key pair as a candidate, and adopts it only if the ratchet actually
//! took a DH step (observed through `State::sending_public`).

use rand_core::{CryptoRng, RngCore};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use super::{
    PreKeyBundle, SessionError, associated_data, decode_ec, encode_ec, encode_kem,
    initiator_shared_secret, is_canonical_key, responder_shared_secret,
};
use tacenta_spqr::{Direction, SpqrError};
use tacenta_triple::TripleError;

use crate::primitives::aead;
use crate::primitives::{dh, kem, xeddsa};
use crate::ratchet;
use crate::ratchet::RatchetError;
use crate::serialization::composite::{AgreementType, Codeword, Composite};
use crate::serialization::{
    ABSENT_ID, DecodeError, MessageType, concat_ad, decode_initial, decode_message, encode_initial,
    encode_message, message_type,
};

/// A long-term identity. The one X25519 key serves both the Diffie-Hellman
/// agreements and the XEdDSA prekey signatures (ADR-0002).
///
/// Erased on drop. This is the longest-lived secret a party holds, so it must
/// not outlive its last use in memory.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct Identity {
    secret: [u8; 32],
}

impl Identity {
    /// Generate a fresh identity.
    pub fn generate<R: RngCore + CryptoRng>(rng: &mut R) -> Identity {
        let mut secret = [0u8; 32];
        rng.fill_bytes(&mut secret);
        Identity { secret }
    }

    fn dh_key(&self) -> dh::PrivateKey {
        dh::PrivateKey::from_bytes(self.secret)
    }

    /// The public identity key, published to peers.
    pub fn public(&self) -> dh::PublicKeyBytes {
        self.dh_key().public_key()
    }

    fn sign<R: RngCore + CryptoRng>(&self, message: &[u8], rng: &mut R) -> [u8; 64] {
        xeddsa::sign(&self.secret, message, rng)
    }

    /// Sign a message under this identity, for callers outside the handshake.
    ///
    /// A transport that authenticates a device by challenge needs this: the
    /// server issues a challenge and the client proves possession of the
    /// identity by signing it. Verified with
    /// [`verify_under_identity`](super::verify_under_identity).
    ///
    /// Distinct from the private `sign`, which signs prekeys as part of the
    /// handshake, and distinct *cryptographically* rather than only by name:
    /// this signs a domain-separated input, so a signature made here cannot
    /// verify as a prekey signature and a prekey signature cannot answer a
    /// challenge. See `APPLICATION_SIGNING_LABEL` for why only this side
    /// carries the tag.
    pub fn sign_message<R: RngCore + CryptoRng>(&self, message: &[u8], rng: &mut R) -> [u8; 64] {
        self.sign(&super::application_signing_input(message), rng)
    }

    /// Serialize the identity secret, so a client can reconnect as the same
    /// party rather than a new one.
    ///
    /// **This is a private key.** It is returned in memory that erases when
    /// dropped, and a caller that persists it is persisting the whole identity:
    /// anyone holding these bytes is this party.
    pub fn export(&self) -> Zeroizing<[u8; 32]> {
        Zeroizing::new(self.secret)
    }

    /// Restore an identity from [`export`](Identity::export).
    ///
    /// Prekeys and sessions are not carried: this is the identity alone, and a
    /// restored party publishes fresh prekeys and re-establishes sessions.
    pub fn from_secret(secret: [u8; 32]) -> Identity {
        Identity { secret }
    }

    /// Create a prekey store: a signed curve prekey, some one-time curve
    /// prekeys, a signed last-resort KEM prekey, and some one-time KEM prekeys,
    /// each with an identifier, signed under this identity.
    ///
    /// `one_time_count` sizes both one-time sets, because a bundle hands out at
    /// most one of each, so they are consumed at the same rate. The last-resort
    /// KEM prekey is what a bundle falls back to once the one-time KEM prekeys
    /// run out, which happens when bundles are fetched faster than they are
    /// replenished (session-establishment.md, Keys).
    ///
    /// Identifiers stop before `u32::MAX`, as they do for `replenish`
    /// (key-deletion.md). The most one-time prekeys of each kind the
    /// identifier space can number is 2^31 - 2. A larger `one_time_count`
    /// makes that many and leaves `next_id` at `u32::MAX`, where `replenish`
    /// and the rotations add nothing. No store that size fits in memory, so
    /// this never shortens a real store. It exists so that no count can wrap
    /// the counter to zero and give a store duplicate identifiers.
    pub fn create_prekeys<R: RngCore + CryptoRng>(
        &self,
        one_time_count: usize,
        rng: &mut R,
    ) -> PrekeyStore {
        // Identifiers start at one because zero is the absent-identifier
        // sentinel. The counter is returned in the store so that replenishment
        // continues from here; see `PrekeyStore::next_id`. They are worked out
        // before any key is made, so the key generation below only takes them.
        let numbering = PrekeyNumbering::for_count(one_time_count);

        let signed_prekey_secret = random_secret(rng);
        let signed_prekey_id = numbering.signed_prekey;
        let signed_prekey_pub = dh::PrivateKey::from_bytes(signed_prekey_secret).public_key();
        let signed_prekey_sig = self.sign(&encode_ec(&signed_prekey_pub), rng);

        let one_time = numbering
            .one_time
            .map(|id| (id, random_secret(rng)))
            .collect();

        let kem = kem::KeyPair::generate(rng);
        let kem_id = numbering.kem;
        let kem_sig = self.sign(&encode_kem(&kem.public_key()), rng);

        // Every KEM prekey is signed individually, unlike the one-time curve
        // prekeys, which are not signed at all. That asymmetry is the
        // specification's, not ours.
        let kem_one_time = numbering
            .kem_one_time
            .map(|id| {
                let pair = kem::KeyPair::generate(rng);
                let sig = self.sign(&encode_kem(&pair.public_key()), rng);
                (id, pair, sig)
            })
            .collect();

        PrekeyStore {
            next_id: numbering.next_id,
            identity_public: self.public(),
            signed_prekey_secret,
            signed_prekey_id,
            signed_prekey_sig,
            one_time,
            kem,
            kem_id,
            kem_sig,
            kem_one_time,
            previous_signed_prekey: None,
            previous_kem: None,
            last_resort_seen: Vec::new(),
        }
    }
}

/// How many spent last-resort handshakes a store remembers **per live
/// last-resort KEM key**: the current one, and the one a rotation retired.
///
/// 1024 tagged fingerprints is 36 KB, which is small beside a single 14 KB
/// session and generous beside the number of peers that should ever reach the
/// last-resort path at all -- they only do so once one-time KEM prekeys are
/// exhausted. Chosen to be comfortably larger than any realistic burst rather
/// than tuned. Two keys can decrypt at once, so the record's worst case is two
/// full budgets, 72 KB, and only between the rotation that retires a key and
/// the one that wipes it.
///
/// A full budget costs availability, not correctness: a new last-resort
/// handshake naming a key whose 1024 entries are already in the record is
/// refused with `Error::LastResortRecordFull` instead of evicting an older
/// entry, because eviction is what let anyone holding the public bundle forget
/// a victim's fingerprint on demand (the note on `PrekeyStore::last_resort_seen`
/// says how). The cost falls on the last-resort path only; a handshake that
/// names a one-time KEM prekey never consults the record. The operator's two
/// levers are keeping one-time KEM prekeys stocked (`replenish`), which keeps
/// peers off this path, and rotating the last-resort key (`rotate_kem`), which
/// gives the new key a budget of its own straight away.
///
/// **Why the bound is counted per key.** A single bound shared between the two
/// live keys made the second lever a lie for one rotation: the retired key's
/// entries stayed, so the rotation that retired it freed nothing, and only the
/// rotation *after* it -- which wipes that key -- released anything. An
/// operator told to rotate to relieve a full record saw no relief until they
/// rotated twice, which the rotation cadence makes slow, and rotating twice in
/// quick succession is the thing `rotate_signed_prekey` warns against. Counting
/// per key makes one rotation enough: the bundle a directory hands out after it
/// names the new key, so every handshake that follows is counted against an
/// empty budget, while the retired key's entries keep their own budget and
/// still refuse every replay against the key that can still decrypt them.
///
/// Rotation is relief, not a reset, against an attacker who is filling the
/// record on purpose. The new bundle is what they fetch too, a last-resort
/// handshake costs well under a millisecond on a current laptop, and they
/// need nothing but the public bundle, so a fresh budget goes again in a
/// fraction of a second. Nothing in this tree pins that figure to a
/// benchmark, and it is the direction rather than the number that matters:
/// the work is on the attacker's cheap side. What holds durably is
/// what stops the handshakes arriving at that rate: a directory that
/// rate-limits bundle fetches, and one-time KEM prekeys kept stocked so that
/// first contacts do not land here at all. `last_resort_record_remaining` is
/// the count to watch for both.
const MAX_LAST_RESORT_SEEN: usize = 1024;

/// A domain-separated fingerprint of the handshake half of an initial message.
///
/// It covers the fields that vary per handshake among those that determine
/// `SK`: both public keys, the KEM ciphertext, and the two prekey identifiers.
/// The signed prekey identifier is bound by `SK` itself and is not included.
/// The ratchet message is left out on purpose -- it is authenticated under
/// keys derived from `SK`, so an attacker cannot vary it and still be
/// accepted, and including it would let a replay evade the check by being
/// re-framed.
///
/// HMAC-SHA256 under a fixed label rather than a bare hash, because the label
/// is what stops a fingerprint from colliding with any other digest this
/// repository computes over overlapping bytes. There is no secret here and it
/// is not a MAC: the input is entirely public.
///
/// The label is a named constant so that `tooling/check-labels.sh` finds it
/// and `LABELS.md` registers it; as an inline literal it was outside the
/// registry that claims to hold every domain-separation string.
const LAST_RESORT_HANDSHAKE_LABEL: &[u8] = b"tacenta last-resort handshake v1";

fn last_resort_fingerprint(decoded: &crate::serialization::DecodedInitial) -> [u8; 32] {
    let mut input = Vec::new();
    input.extend_from_slice(&(decoded.identity.len() as u32).to_be_bytes());
    input.extend_from_slice(&decoded.identity);
    input.extend_from_slice(&(decoded.ephemeral.len() as u32).to_be_bytes());
    input.extend_from_slice(&decoded.ephemeral);
    input.extend_from_slice(&(decoded.kem_ciphertext.len() as u32).to_be_bytes());
    input.extend_from_slice(&decoded.kem_ciphertext);
    input.extend_from_slice(&decoded.one_time_prekey_id.to_be_bytes());
    input.extend_from_slice(&decoded.kem_prekey_id.to_be_bytes());
    crate::primitives::kdf::hmac_sha256(LAST_RESORT_HANDSHAKE_LABEL, &input)
}

/// The identifiers `create_prekeys` numbers a store with, in the order
/// key-deletion.md gives: the signed prekey, the one-time curve prekeys, the
/// last-resort KEM prekey, the one-time KEM prekeys, and the `next_id` left
/// after them. Kept apart from the key generation so that the arithmetic at
/// the end of the identifier space can be checked without making the keys.
#[derive(Debug, PartialEq, Eq)]
struct PrekeyNumbering {
    signed_prekey: u32,
    one_time: core::ops::Range<u32>,
    kem: u32,
    kem_one_time: core::ops::Range<u32>,
    next_id: u32,
}

/// The most one-time prekeys of each kind `create_prekeys` makes, 2^31 - 2.
/// This is the largest `n` whose numbering fits a `u32`: identifiers `1` to
/// `2n + 2`, with `next_id` at `2n + 3`. At this `n`, `next_id` is `u32::MAX`,
/// the point where `replenish` and the rotations stop, so `u32::MAX` is never
/// issued.
const MAX_CREATED_ONE_TIME: u32 = (u32::MAX - 3) / 2;

impl PrekeyNumbering {
    /// The numbering for `one_time_count` one-time prekeys of each kind, with
    /// the count capped at `MAX_CREATED_ONE_TIME`.
    fn for_count(one_time_count: usize) -> PrekeyNumbering {
        let n = u32::try_from(one_time_count)
            .unwrap_or(u32::MAX)
            .min(MAX_CREATED_ONE_TIME);
        // Under the cap `checked` is never `None`, and a test pins the cap as
        // the largest count for which it is `Some`. The fallback is there so
        // that a wrong cap would give a store with no one-time prekeys, never
        // a panic or a wrapped identifier.
        PrekeyNumbering::checked(n).unwrap_or(PrekeyNumbering {
            signed_prekey: 1,
            one_time: 2..2,
            kem: 2,
            kem_one_time: 3..3,
            next_id: 3,
        })
    }

    /// The numbering for exactly `n` one-time prekeys of each kind, or `None`
    /// if `next_id` would pass the end of the identifier space.
    fn checked(n: u32) -> Option<PrekeyNumbering> {
        let kem = n.checked_add(2)?;
        let kem_one_time_start = kem.checked_add(1)?;
        let next_id = kem_one_time_start.checked_add(n)?;
        Some(PrekeyNumbering {
            signed_prekey: 1,
            one_time: 2..kem,
            kem,
            kem_one_time: kem_one_time_start..next_id,
            next_id,
        })
    }
}

fn random_secret<R: RngCore + CryptoRng>(rng: &mut R) -> [u8; 32] {
    let mut s = [0u8; 32];
    rng.fill_bytes(&mut s);
    s
}

/// Which skipped-key store a receive failure says is full. The two ratchets
/// report it with different error types, and `Session::decrypt` evicts from
/// the one that complained (see the loop in `decrypt_ratchet`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum FullStore {
    Classical,
    PostQuantum,
}

fn full_store(e: &TripleError) -> Option<FullStore> {
    match e {
        TripleError::Classical(RatchetError::SkippedStoreFull) => Some(FullStore::Classical),
        TripleError::PostQuantum(SpqrError::SkippedStoreFull) => Some(FullStore::PostQuantum),
        _ => None,
    }
}

/// A party's own prekeys and the private keys behind them. Curve keys are kept as
/// raw secrets so a session can both agree with them and adopt one as its initial
/// ratchet key.
pub struct PrekeyStore {
    identity_public: dh::PublicKeyBytes,
    signed_prekey_secret: [u8; 32],
    signed_prekey_id: u32,
    signed_prekey_sig: [u8; 64],
    one_time: Vec<(u32, [u8; 32])>,
    kem: kem::KeyPair,
    kem_id: u32,
    kem_sig: [u8; 64],
    /// One-time KEM prekeys, each with its own identifier and signature. Handed
    /// out in preference to the last-resort key above, and deleted on use.
    kem_one_time: Vec<(u32, kem::KeyPair, [u8; 64])>,
    /// The signed curve prekey this store held before its last
    /// `rotate_signed_prekey`, kept for one rotation so that a bundle a peer
    /// fetched just before the rotation still establishes. `None` until the
    /// first rotation; replaced, and the older secret wiped, by the next.
    previous_signed_prekey: Option<([u8; 32], u32, [u8; 64])>,
    /// The last-resort KEM prekey before the last `rotate_kem`, kept on the
    /// same terms. The replay record below follows it: entries recorded under
    /// this key stay while it can still decrypt, since a replay against the
    /// retired key is still a replay, and are dropped when the next rotation
    /// wipes it.
    previous_kem: Option<(kem::KeyPair, u32, [u8; 64])>,
    /// The next identifier to hand out, so that anything adding keys to this
    /// store continues the sequence rather than restarting it.
    ///
    /// **The identifiers in a store must be unique, and nothing about a `Vec`
    /// enforces that.** Both `take_one_time` and `take_one_time_kem` find the
    /// *first* entry with a given identifier. Two entries sharing one means
    /// removing the first exposes the second, so a replayed initial message
    /// naming that identifier is served twice -- which is precisely what a
    /// one-time prekey exists to prevent.
    ///
    /// Nothing produces a duplicate. `create_prekeys` numbers a whole store in
    /// one pass, and `replenish`, `rotate_signed_prekey` and `rotate_kem` each
    /// take their identifiers from this counter. The obvious other way to
    /// refill a store is to call `create_prekeys` again and combine the
    /// results, which restarts the identifiers at one so that they collide
    /// (`two_stores_from_one_identity_collide_and_must_not_be_merged` pins
    /// that). This field is what lets anything that adds keys continue the
    /// sequence instead.
    ///
    /// The counter has an end. `u32::MAX` is never issued: `create_prekeys`
    /// leaves the counter at most there, and `replenish` and the rotations add
    /// nothing once it stands there (key-deletion.md).
    next_id: u32,
    /// The last-resort handshakes this store has already accepted: for each,
    /// the identifier of the last-resort KEM key it was made against and the
    /// fingerprint of the handshake, newest last, at most
    /// `MAX_LAST_RESORT_SEEN` **per key**.
    ///
    /// **What this is for.** A one-time KEM prekey defends itself: it is
    /// deleted on use, so replaying an initial message that names one fails
    /// with `UnknownPrekeyId`. The last-resort key is reusable by design and
    /// has no such defence. Without this record a captured initial message
    /// naming it -- with no one-time curve prekey either, which is the steady
    /// state of a store whose one-time pools are exhausted -- would be
    /// accepted again on every delivery, and each acceptance hands the
    /// application the initiator's first plaintext a second time, as the
    /// opening message of what looks like a fresh session. That is duplicate
    /// delivery, not merely a denial of service: the same message is received
    /// twice, under two sessions, and nothing marks the second as a repeat.
    /// The attacker learns nothing and cannot speak on either session; the
    /// harm is to the application's record of what was said, and how often.
    ///
    /// The specification is aware that the handshake replays: without a
    /// one-time *curve* prekey Bob derives the same `SK` in different runs,
    /// which is why the ratchet must randomise before he replies
    /// (session-establishment.md, "Replay, and why the ratchet must follow").
    /// That reasoning is about key reuse. It says nothing about the replay
    /// being accepted at all, which is what this refuses.
    ///
    /// **Why the bound is per key lifetime, and why it fails closed.** This
    /// was once a window of the last `MAX_LAST_RESORT_SEEN` fingerprints,
    /// oldest evicted first. A window is a count an unauthenticated peer can
    /// drive: anyone holding the public bundle can complete a last-resort
    /// handshake under a fresh identity in well under a millisecond on a
    /// current laptop, so a thousand of them evicted a chosen victim's
    /// fingerprint in a fraction of a second, after which the captured
    /// message replayed. Now the record
    /// holds entries only for keys that can still decrypt -- the current
    /// last-resort key and, after a rotation, the retired one -- each tagged
    /// with the key it was made against, and a key's entries are dropped when
    /// `rotate_kem` wipes that key, because a message naming a wiped key fails
    /// with `UnknownPrekeyId` before the record is consulted. What the bound
    /// measures is therefore how many distinct last-resort handshakes one key
    /// has accepted over its lifetime, not how many arrived recently.
    ///
    /// **The budget is each key's own.** The bound is counted over the entries
    /// tagged with the key a handshake names, not over the record as a whole,
    /// so the two live keys never compete for room and the worst case is two
    /// full budgets rather than one. That is what makes rotation the lever it
    /// is documented as: the rotation that retires a key leaves its entries
    /// alone, and the new key -- the one every bundle fetched afterwards names
    /// -- starts empty, so relief arrives on the first rotation instead of the
    /// second. Under one shared bound the first rotation freed nothing at all,
    /// because the retired key's entries stayed and still filled it.
    ///
    /// Rotation is still relief and not a reset against an attacker who is
    /// filling the record on purpose: the new bundle is the one they fetch
    /// too, and at well under a millisecond per last-resort handshake on a
    /// current laptop -- a figure no benchmark in this tree pins, and quoted
    /// only for its direction -- a fresh budget goes again in a fraction of a
    /// second. The defences that hold are the ones
    /// that keep the handshakes from arriving at that rate -- a directory
    /// that rate-limits bundle fetches, and one-time KEM prekeys kept stocked
    /// -- and `last_resort_record_remaining` is what says whether they are
    /// holding.
    ///
    /// When a key's budget is spent, a last-resort handshake naming that key
    /// whose fingerprint is not in the record is refused with
    /// `Error::LastResortRecordFull` before anything is decrypted or changed.
    /// Nothing is evicted, ever: an entry leaves the record only when its key
    /// is wiped. A fingerprint already in the record is refused as
    /// `ReplayedLastResort` whether or not any budget is spent. The refusal is
    /// the honest cost of a bound: a store that ran out of one-time KEM
    /// prekeys and then accepted 1024 last-resort first contacts under one key
    /// stops accepting more under that key until a rotation moves new
    /// handshakes onto a fresh one, and every other path is untouched.
    /// Keeping one-time KEM prekeys stocked (`replenish`) is what keeps the
    /// last-resort path rare enough for the bound never to be reached; this
    /// record is the backstop for when it is not.
    ///
    /// The fingerprint alone decides whether a handshake is a repeat: it
    /// covers the KEM prekey identifier, so two entries with one fingerprint
    /// would be one handshake. The tag is for pruning. That is also why a
    /// store upgraded from a format that did not tag its entries can tag them
    /// all with the current key's identifier and still refuse every replay it
    /// refused before: the tag only decides when an entry is dropped, and an
    /// entry dropped a rotation late is harmless.
    last_resort_seen: Vec<(u32, [u8; 32])>,
}

/// Erased on drop, by hand rather than by derive.
///
/// A `#[derive(Zeroize)]` over the whole struct will not compile: several
/// fields are not `Zeroize` at all -- the identity's *public* key, and the
/// `kem::KeyPair`s, which erase themselves through their own `Drop` rather than
/// through `Zeroize`. (`zeroize` 1.9 does implement `Zeroize` for tuples, so
/// the two one-time vectors of tuples are not the obstacle; the un-`Zeroize`
/// field types are.) Writing the destructor out lets it wipe exactly the secret
/// fields and leave the rest, which is the same answer `tacenta_spqr::State`
/// gives one crate over.
///
/// So this wipes only what is secret and not already self-wiping: the signed
/// prekey secret, the retired signed prekey secret, and the one-time curve
/// secrets. The KEM key pairs are left to their own erasure -- dropping the
/// vectors that hold them wipes them -- and the identifiers, the identity's
/// public key, and the signatures are public and left alone.
impl Drop for PrekeyStore {
    fn drop(&mut self) {
        self.signed_prekey_secret.zeroize();
        if let Some((secret, _, _)) = self.previous_signed_prekey.as_mut() {
            secret.zeroize();
        }
        for (_, secret) in self.one_time.iter_mut() {
            secret.zeroize();
        }
    }
}

/// Asserted, since the destructor above is what provides it.
impl ZeroizeOnDrop for PrekeyStore {}

/// A published bundle: the public keys and signatures, plus the identifiers a
/// recipient echoes back so the publisher can find the matching private keys.
pub struct PublishedBundle {
    pub bundle: PreKeyBundle,
    pub signed_prekey_id: u32,
    pub one_time_prekey_id: u32,
    pub kem_prekey_id: u32,
}

impl PrekeyStore {
    /// Hand out a bundle: one one-time curve prekey if any remain, and one KEM
    /// prekey, preferring a one-time key over the last-resort one. The private
    /// keys stay in the store until a message actually uses them (see
    /// `establish_responder`), which is when they are deleted for forward
    /// secrecy.
    ///
    /// **Serve the result to one requester.** This returns the *same* one-time
    /// prekey on every call until a message consumes it, so a directory that
    /// hands one `publish()` result to two peers strands the second: their
    /// initial message names a prekey the first peer's message has already
    /// deleted, it fails with `UnknownPrekeyId`, and because an initiator
    /// repeats its initial message until answered, that peer never recovers
    /// without being re-bundled. A directory serving many requesters should
    /// stock a pool with `publish_one_time_batch` and dispense from it, which
    /// is the intended shape.
    pub fn publish(&self) -> PublishedBundle {
        let (one_time_prekey_id, one_time_prekey) = match self.one_time.last() {
            Some((id, secret)) => (*id, Some(dh::PrivateKey::from_bytes(*secret).public_key())),
            None => (ABSENT_ID, None),
        };
        // Prefer a one-time KEM prekey; fall back to the last-resort key only
        // once they are exhausted (session-establishment.md, Sending the
        // initial message).
        let (kem_prekey_id, kem_prekey, kem_prekey_signature) = match self.kem_one_time.last() {
            Some((id, pair, sig)) => (*id, pair.public_key(), *sig),
            None => (self.kem_id, self.kem.public_key(), self.kem_sig),
        };
        PublishedBundle {
            bundle: PreKeyBundle {
                identity_key: self.identity_public,
                signed_prekey: dh::PrivateKey::from_bytes(self.signed_prekey_secret).public_key(),
                signed_prekey_signature: self.signed_prekey_sig,
                kem_prekey,
                kem_prekey_signature,
                one_time_prekey,
            },
            signed_prekey_id: self.signed_prekey_id,
            one_time_prekey_id,
            kem_prekey_id,
        }
    }

    /// Add `count` fresh one-time prekeys of each kind, continuing the
    /// identifier sequence rather than restarting it.
    ///
    /// **The other half of last-resort replay marking.** A store publishes one-time KEM prekeys in
    /// preference to the reusable last-resort key and deletes each on use, so
    /// without replenishment a party has exactly as many post-quantum-forward
    /// first contacts as `create_prekeys` gave it, and every peer after that
    /// lands on the last-resort
    /// path. That path is the weaker one on both counts: no one-time forward
    /// secrecy, and it is the one `last_resort_seen` has to bound because it
    /// cannot defend itself by deletion.
    ///
    /// Takes the `Identity` because each KEM prekey carries its own signature,
    /// and a store cannot sign for itself -- it holds no signing key, which is
    /// deliberate.
    ///
    /// The trap this exists to avoid is the obvious implementation: calling
    /// `create_prekeys` again and merging. That numbers the new batch from one,
    /// so identifiers collide, and since both `take_one_time` and
    /// `take_one_time_kem` find the *first* entry with an identifier, removing
    /// one exposes another under the same name -- a one-time prekey served
    /// twice, which is the whole thing it exists to prevent. Continuing from
    /// `next_id` is what makes that impossible. See the note on the field.
    ///
    /// **Refused quietly when `identity` is not this store's** -- when
    /// `identity.public()` differs from the stored `identity_public`. Signing
    /// under any other identity builds a store that publishes bundles every
    /// initiator refuses and that `from_bytes` then refuses as `Incoherent`;
    /// nothing is changed on that path. See `rotate_signed_prekey`.
    pub fn replenish<R: RngCore + CryptoRng>(
        &mut self,
        identity: &Identity,
        count: usize,
        rng: &mut R,
    ) {
        // The store's signatures are only meaningful under the identity whose
        // public key it holds (session-persistence.md, Prekey store, Semantic
        // rules: "every operation that signs a prekey signs under the identity
        // whose public key is `identity_public`"). Signing under any other
        // identity builds a state the reader refuses on its next restore --
        // internally consistent by every cheap predicate, and unusable -- so a
        // mismatched identity is refused here, quietly and without changing
        // anything, the same way the exhausted identifier space above is. This
        // is the operations half of the sixth semantic rule; `from_bytes`
        // checks the other half over bytes that have already been stored.
        if identity.public() != self.identity_public {
            return;
        }
        // The identifier space is finite, and wrapping it would reach the
        // absent-identifier sentinel and then collide with live entries, the
        // exact trap `next_id`'s own note describes. Unreachable in any real
        // store, so it is refused quietly rather than panicked on: a store
        // that has issued four billion identifiers stops issuing them.
        //
        // Reserved before the loop so the vector never grows mid-push: a `Vec`
        // that outgrows its allocation moves the 32-byte one-time secrets to a
        // larger block and hands the smaller back to the allocator un-wiped,
        // which the hand-written `Drop` cannot reach (CR-15). The same reason
        // `to_bytes` sizes its buffer up front.
        self.one_time.reserve_exact(count);
        for _ in 0..count {
            let Some(next) = self.next_id.checked_add(1) else {
                return;
            };
            let id = self.next_id;
            self.next_id = next;
            self.one_time.push((id, random_secret(rng)));
        }
        self.kem_one_time.reserve_exact(count);
        for _ in 0..count {
            let Some(next) = self.next_id.checked_add(1) else {
                return;
            };
            let pair = kem::KeyPair::generate(rng);
            let sig = identity.sign(&encode_kem(&pair.public_key()), rng);
            let id = self.next_id;
            self.next_id = next;
            self.kem_one_time.push((id, pair, sig));
        }
    }

    /// Replace the signed curve prekey with a fresh one signed under
    /// `identity`, keeping the one it replaces for a single rotation.
    ///
    /// PQXDH has the signed prekey rotated periodically to bound how far back
    /// a compromise of its private half reaches (session-establishment.md,
    /// Keys). A peer who fetched the
    /// bundle just before a rotation still names the old identifier, so the
    /// retired key is honoured for one more rotation and then wiped -- which
    /// makes the rotation cadence the grace period, and means a rotation
    /// should not be run twice in quick succession while bundles are in
    /// flight. Persist the store after rotating, and republish.
    ///
    /// **A dispensed one-time pool does not survive two rotations.**
    /// `publish_one_time_batch` stamps every bundle it hands a directory with
    /// the signed-prekey identifier current at stocking time, and a directory
    /// keeps them until each is fetched. After the *second* rotation every
    /// bundle still in that pool names a retired identifier and fails with
    /// `UnknownPrekeyId`; an initiator repeats its initial message until
    /// answered, so such a peer never recovers. The one-time secrets those
    /// bundles named stay in this store unconsumed (they are counted by
    /// `one_time_remaining` and persisted by `to_bytes`), harmless but idle.
    /// So: restock the directory from a fresh `publish_one_time_batch` after
    /// every rotation, and never rotate twice inside one directory refresh
    /// cycle.
    ///
    /// Refused quietly at the end of the identifier space, like `replenish`.
    ///
    /// **Refused quietly, too, when `identity` is not the identity this store
    /// was created under** -- that is, when `identity.public()` differs from
    /// the stored `identity_public`. Signing a prekey under any other identity
    /// builds a store that publishes bundles every initiator refuses, and that
    /// `from_bytes` refuses on its next restore (session-persistence.md,
    /// Prekey store, Semantic rules). Nothing is changed on that path.
    pub fn rotate_signed_prekey<R: RngCore + CryptoRng>(
        &mut self,
        identity: &Identity,
        rng: &mut R,
    ) {
        let Some(next) = self.next_id.checked_add(1) else {
            return;
        };
        // The store's signatures are only meaningful under the identity whose
        // public key it holds (session-persistence.md, Prekey store, Semantic
        // rules: "every operation that signs a prekey signs under the identity
        // whose public key is `identity_public`"). Signing under any other
        // identity builds a state the reader refuses on its next restore --
        // internally consistent by every cheap predicate, and unusable -- so a
        // mismatched identity is refused here, quietly and without changing
        // anything, the same way the exhausted identifier space above is. This
        // is the operations half of the sixth semantic rule; `from_bytes`
        // checks the other half over bytes that have already been stored.
        if identity.public() != self.identity_public {
            return;
        }
        let secret = random_secret(rng);
        let id = self.next_id;
        self.next_id = next;
        let public = dh::PrivateKey::from_bytes(secret).public_key();
        let sig = identity.sign(&encode_ec(&public), rng);
        // The key being retired becomes the previous one, and the previous one,
        // if any, is wiped. Honest limit: the secrets are `Copy` arrays, so the
        // stack copies this shuffle makes (`secret` before it is stored, the
        // `retired` tuple before it is moved) are outside reach, the same
        // limit `create_prekeys` and LIMITATIONS.md's "copies the language
        // makes" already state.
        let retired = (
            self.signed_prekey_secret,
            self.signed_prekey_id,
            self.signed_prekey_sig,
        );
        if let Some((mut old, _, _)) = self.previous_signed_prekey.replace(retired) {
            old.zeroize();
        }
        self.signed_prekey_secret = secret;
        self.signed_prekey_id = id;
        self.signed_prekey_sig = sig;
    }

    /// Replace the last-resort KEM prekey the same way, for the same reason,
    /// and with more at stake: it is reusable by design, so it is the one
    /// prekey whose compromise reaches every last-resort handshake made under
    /// it.
    ///
    /// The replay record follows the keys. Entries recorded under the key
    /// being retired stay, since a message naming it still decrypts for one
    /// more rotation and a replay against it is still a replay. Entries
    /// recorded under the key this rotation *wipes* -- the one the previous
    /// rotation retired -- are dropped here, because a message naming a wiped
    /// key fails with `UnknownPrekeyId` before the record is consulted, so
    /// they can refuse nothing and would only take up room in the file.
    ///
    /// This is also the lever against a full record, and it works on the first
    /// rotation rather than the second: `MAX_LAST_RESORT_SEEN` is counted per
    /// key, so the key opened here starts with an empty budget, and the bundle
    /// a directory hands out from now on names it. The retired key's entries
    /// are neither freed nor in the new key's way; they are released when the
    /// next rotation wipes that key.
    ///
    /// **Refused quietly when `identity` is not this store's** -- when
    /// `identity.public()` differs from the stored `identity_public`. Signing
    /// under any other identity builds a store that publishes bundles every
    /// initiator refuses and that `from_bytes` then refuses as `Incoherent`;
    /// nothing is changed on that path. See `rotate_signed_prekey`.
    pub fn rotate_kem<R: RngCore + CryptoRng>(&mut self, identity: &Identity, rng: &mut R) {
        let Some(next) = self.next_id.checked_add(1) else {
            return;
        };
        // The store's signatures are only meaningful under the identity whose
        // public key it holds (session-persistence.md, Prekey store, Semantic
        // rules: "every operation that signs a prekey signs under the identity
        // whose public key is `identity_public`"). Signing under any other
        // identity builds a state the reader refuses on its next restore --
        // internally consistent by every cheap predicate, and unusable -- so a
        // mismatched identity is refused here, quietly and without changing
        // anything, the same way the exhausted identifier space above is. This
        // is the operations half of the sixth semantic rule; `from_bytes`
        // checks the other half over bytes that have already been stored.
        if identity.public() != self.identity_public {
            return;
        }
        let pair = kem::KeyPair::generate(rng);
        let id = self.next_id;
        self.next_id = next;
        let sig = identity.sign(&encode_kem(&pair.public_key()), rng);
        let retired = core::mem::replace(&mut self.kem, pair);
        // `kem::KeyPair` erases itself when dropped, so the pair `replace`
        // hands back -- the one retired two rotations ago -- needs no help to
        // be wiped; it is dropped at the end of this statement. Its identifier
        // is what the record is pruned by, and identifiers are never reused
        // within a store (`next_id`), so nothing live shares it.
        if let Some((_, wiped_id, _)) =
            self.previous_kem
                .replace((retired, self.kem_id, self.kem_sig))
        {
            self.last_resort_seen.retain(|(id, _)| *id != wiped_id);
        }
        self.kem_id = id;
        self.kem_sig = sig;
    }

    /// How many one-time prekeys of each kind remain, curve then KEM.
    ///
    /// What a caller polls to decide whether to `replenish`. The two counts are
    /// reported separately because they are consumed separately: an initial
    /// message may name a KEM one-time prekey and no curve one.
    pub fn one_time_remaining(&self) -> (usize, usize) {
        (self.one_time.len(), self.kem_one_time.len())
    }

    /// How many more last-resort handshakes this store's **current**
    /// last-resort KEM key can accept before `establish_responder` refuses
    /// them with `Error::LastResortRecordFull`.
    ///
    /// The bound is per key, so a single number has to pick one, and this
    /// picks the current key rather than reporting a per-key figure for each
    /// or a total across both. Two reasons. The published bundle names the
    /// current key, so every handshake a peer can make from here on is
    /// counted against this budget and no other: this is the number that says
    /// whether the next arrival will be accepted. And the retired key's
    /// budget is not a lever anyone can pull -- it only shrinks, by
    /// handshakes made against a bundle fetched before the last rotation, and
    /// it is released wholesale by the next one -- so an operator watching it
    /// would learn nothing they could act on. A caller who does want the
    /// retired key's occupancy asks for it by identifier with
    /// `last_resort_record_remaining_for`.
    ///
    /// **What one number cannot say.** Straight after a rotation this reads
    /// the full budget, and the record may at that moment hold a spent 1024
    /// entries under the retired key -- half of the 2048 the two live budgets
    /// allow. Nothing in the figure is wrong: the next arrival really does
    /// have a full budget, because it names the new key. But an operator
    /// polling only this one sees the relief and not what is still occupied,
    /// and the retired key's entries leave only when the next rotation wipes
    /// that key. `last_resort_record_remaining_for` is what shows the other
    /// half.
    ///
    /// The signal for the two levers `MAX_LAST_RESORT_SEEN` names. A count
    /// that keeps falling means first contacts are landing on the last-resort
    /// path, so one-time KEM prekeys need restocking (`replenish`;
    /// `one_time_remaining` says how many are left). A count that falls
    /// faster than peers could plausibly arrive is someone filling the record
    /// on purpose, which is the directory's rate limit on bundle fetches to
    /// stop; `rotate_kem` restores this number to the full budget at once,
    /// but only for as long as they take to spend it again.
    pub fn last_resort_record_remaining(&self) -> usize {
        // No key's entries exceed the bound -- a handshake that would take one
        // past is refused, and `from_bytes` refuses a file where any key's do
        // -- so this never saturates; saturating anyway rather than trusting
        // that here.
        MAX_LAST_RESORT_SEEN.saturating_sub(self.last_resort_seen_for(self.kem_id))
    }

    /// How many more last-resort handshakes the last-resort KEM key named by
    /// `key_id` can accept, or `None` when that identifier is neither of the
    /// two the store can still decrypt for.
    ///
    /// The per-key figure `last_resort_record_remaining` has to leave out.
    /// Both budgets are real -- a handshake is refused against the key it
    /// names, not against the record -- so an operator who wants the whole
    /// picture after a rotation needs the retired key's number as well as the
    /// current one, and the identifiers to ask with are the `kem_prekey_id`
    /// of the bundles the store published.
    ///
    /// `None` rather than the full budget for anything else, and the
    /// distinction matters: an identifier this store never issued, or one a
    /// rotation has wiped, has no budget rather than an untouched one, and a
    /// handshake naming it is refused with `UnknownPrekeyId` before the
    /// record is reached at all.
    pub fn last_resort_record_remaining_for(&self, key_id: u32) -> Option<usize> {
        let live = key_id == self.kem_id
            || self
                .previous_kem
                .as_ref()
                .is_some_and(|(_, id, _)| *id == key_id);
        if !live {
            return None;
        }
        Some(MAX_LAST_RESORT_SEEN.saturating_sub(self.last_resort_seen_for(key_id)))
    }

    /// How many record entries are tagged with one last-resort KEM key.
    ///
    /// The quantity `MAX_LAST_RESORT_SEEN` bounds. A linear scan of a vector
    /// holding at most two budgets, run once per last-resort handshake and
    /// never on the one-time path, which is the same shape as the replay scan
    /// beside it in `establish_responder` and for the same reason: the record
    /// is a vector rather than a map so that it stays in the translatable
    /// subset, as the note on the field says.
    fn last_resort_seen_for(&self, key_id: u32) -> usize {
        self.last_resort_seen
            .iter()
            .filter(|(id, _)| *id == key_id)
            .count()
    }

    /// One published bundle per one-time pair the store still holds, for a
    /// directory that dispenses them.
    ///
    /// **This is what `publish` cannot do.** `publish` returns *the* bundle,
    /// and it has to pick one one-time prekey to put in it, so every requester
    /// between now and the first authenticated use is handed the same one.
    /// That is sound only where a bundle is fetched once. A dispensing
    /// directory wants them all up front, hands out each exactly once, and
    /// falls back to `publish_multi_use` when it runs out.
    ///
    /// Pairs a one-time curve prekey with a one-time KEM prekey, so a
    /// dispensed bundle carries both and neither is reused. The batch is as
    /// long as the shorter of the two pools; the private halves stay here
    /// until an authenticated message consumes them, exactly as before.
    pub fn publish_one_time_batch(&self) -> Vec<PublishedBundle> {
        self.one_time
            .iter()
            .rev()
            .zip(self.kem_one_time.iter().rev())
            .map(
                |((otp_id, otp_secret), (kem_id, kem_pair, kem_sig))| PublishedBundle {
                    bundle: PreKeyBundle {
                        identity_key: self.identity_public,
                        signed_prekey: dh::PrivateKey::from_bytes(self.signed_prekey_secret)
                            .public_key(),
                        signed_prekey_signature: self.signed_prekey_sig,
                        kem_prekey: kem_pair.public_key(),
                        kem_prekey_signature: *kem_sig,
                        one_time_prekey: Some(dh::PrivateKey::from_bytes(*otp_secret).public_key()),
                    },
                    signed_prekey_id: self.signed_prekey_id,
                    one_time_prekey_id: *otp_id,
                    kem_prekey_id: *kem_id,
                },
            )
            .collect()
    }

    /// The bundle to serve once the one-time pool is exhausted: no one-time
    /// curve prekey, and the reusable last-resort KEM key.
    ///
    /// Sound rather than a degraded error. The signed prekey and the KEM
    /// last-resort key are multi-use by design, so a bundle of only those can
    /// be served to everyone; what is lost is the extra forward secrecy a
    /// one-time key would have added, which is why `replenish` exists.
    pub fn publish_multi_use(&self) -> PublishedBundle {
        PublishedBundle {
            bundle: PreKeyBundle {
                identity_key: self.identity_public,
                signed_prekey: dh::PrivateKey::from_bytes(self.signed_prekey_secret).public_key(),
                signed_prekey_signature: self.signed_prekey_sig,
                kem_prekey: self.kem.public_key(),
                kem_prekey_signature: self.kem_sig,
                one_time_prekey: None,
            },
            signed_prekey_id: self.signed_prekey_id,
            one_time_prekey_id: ABSENT_ID,
            kem_prekey_id: self.kem_id,
        }
    }

    /// The next identifier this store has not yet handed out.
    ///
    /// What replenishment must continue from. Numbering a fresh batch from one
    /// instead would produce duplicates, and duplicates let a one-time prekey be
    /// used twice; see the note on the field.
    pub fn next_id(&self) -> u32 {
        self.next_id
    }

    /// Delete the one-time prekey with this identifier, wiping it first.
    /// Returns whether one was found.
    ///
    /// The secret is zeroized *in place* before the entry is removed, and
    /// nothing is returned: handing the bare array back to a caller that
    /// discards it would make "deleted" mean "dropped unwiped".
    ///
    /// Removed by zeroize, swap-with-last, then `pop`, rather than by
    /// `swap_remove` (CR-15). `swap_remove` moves the last entry into slot `i`
    /// and truncates, which leaves the moved entry's *original* tail slot
    /// holding a live copy of its secret beyond `len` -- outside the reach of
    /// `Drop`'s `iter_mut`. Swapping first and popping the now-dead tail slot
    /// means the byte range that leaves the vector holds only the zeros written
    /// into the removed entry.
    fn take_one_time(&mut self, id: u32) -> bool {
        match self.one_time.iter().position(|(k, _)| *k == id) {
            Some(i) => {
                self.one_time[i].1.zeroize();
                let last = self.one_time.len() - 1;
                self.one_time.swap(i, last);
                self.one_time.pop();
                true
            }
            None => false,
        }
    }

    /// Read the one-time prekey with this identifier without deleting it.
    ///
    /// The pair to `take_one_time`, and the reason both exist: an initial
    /// message names a prekey before anything has authenticated it, so the key
    /// has to be *read* to attempt decryption and *deleted* only once that
    /// decryption succeeds. Deleting on the way in let anyone holding a
    /// published bundle burn one-time prekeys with a message they could not
    /// have written.
    fn peek_one_time(&self, id: u32) -> Option<Zeroizing<[u8; 32]>> {
        // The copy lives for the rest of `establish_responder`; wrapped so it
        // is wiped when that ends rather than left on the stack.
        self.one_time
            .iter()
            .find(|(k, _)| *k == id)
            .map(|(_, v)| Zeroizing::new(*v))
    }

    /// Borrow the one-time KEM prekey with this identifier without deleting it.
    /// The KEM half of `peek_one_time`, for the same reason.
    ///
    /// A borrow rather than a copy: the caller only needs it to decapsulate,
    /// and handing out an owned copy of a KEM secret to avoid a borrow would be
    /// the wrong trade.
    fn peek_one_time_kem(&self, id: u32) -> Option<&kem::KeyPair> {
        self.kem_one_time
            .iter()
            .find(|(k, _, _)| *k == id)
            .map(|(_, pair, _)| pair)
    }

    /// Remove and return the one-time KEM prekey with this identifier. Removing
    /// it is the deletion the specification requires: a one-time key is used
    /// once and its private half must not outlive that use.
    ///
    /// Swap-with-last then `pop`, the same shape as `take_one_time` (CR-15).
    /// Unlike the curve secrets, a `kem::KeyPair` holds its secret behind a
    /// `Zeroizing<Vec<u8>>`, so the entry moved by the swap leaves only a
    /// moved-from pointer in the dead tail slot, not a copy of the key bytes;
    /// the returned pair carries the sole live copy and erases it when the
    /// caller drops it. Written the same way so the two removals read alike.
    fn take_one_time_kem(&mut self, id: u32) -> Option<kem::KeyPair> {
        let i = self.kem_one_time.iter().position(|(k, _, _)| *k == id)?;
        let last = self.kem_one_time.len() - 1;
        self.kem_one_time.swap(i, last);
        let (_, pair, _) = self.kem_one_time.pop()?;
        Some(pair)
    }

    /// Encode this store for persistence: the version byte, then each field
    /// in declaration order, length-prefixed where its width is not fixed.
    /// Not a message on the wire -- this is what a storage layer writes to
    /// disk and reads back with `from_bytes` after a restart. At-rest
    /// protection of the persisted bytes is that caller's job, the same as
    /// for `Session::export`.
    ///
    /// After `establish_responder`, persist the session it returned *before*
    /// this store, and both before acting on the message: `Session::export`
    /// states the ordering rules and what each crash window costs.
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        // Sized exactly before the first write so the buffer never grows: a
        // `Vec` that outgrows its allocation moves to a larger one and hands
        // the smaller back to the allocator un-wiped, and `Zeroizing` reaches
        // only the allocation alive at the end. The
        // KEM encodings are taken once and reused for the same reason.
        let kem_bytes = self.kem.to_bytes();
        let kem_one_time_bytes: Vec<Zeroizing<Vec<u8>>> = self
            .kem_one_time
            .iter()
            .map(|(_, pair, _)| pair.to_bytes())
            .collect();
        let previous_kem_bytes = self
            .previous_kem
            .as_ref()
            .map(|(pair, _, _)| pair.to_bytes());
        let capacity = 1
            + 32
            + (32 + 4 + 64)
            + 4
            + self.one_time.len() * (4 + 32)
            + (4 + kem_bytes.len())
            + (4 + 64)
            + 4
            + kem_one_time_bytes
                .iter()
                .map(|b| 4 + (4 + b.len()) + 64)
                .sum::<usize>()
            + 4
            + 4
            + self.last_resort_seen.len() * (4 + 32)
            + 1
            + self
                .previous_signed_prekey
                .as_ref()
                .map_or(0, |_| 32 + 4 + 64)
            + 1
            + previous_kem_bytes
                .as_ref()
                .map_or(0, |b| (4 + b.len()) + 4 + 64);
        let mut out = Vec::with_capacity(capacity);
        out.push(PREKEY_STORE_VERSION);
        out.extend_from_slice(self.identity_public.as_bytes());
        out.extend_from_slice(&self.signed_prekey_secret);
        out.extend_from_slice(&self.signed_prekey_id.to_be_bytes());
        out.extend_from_slice(&self.signed_prekey_sig);

        out.extend_from_slice(&(self.one_time.len() as u32).to_be_bytes());
        for (id, secret) in &self.one_time {
            out.extend_from_slice(&id.to_be_bytes());
            out.extend_from_slice(secret);
        }

        push_len_prefixed(&mut out, &kem_bytes);
        out.extend_from_slice(&self.kem_id.to_be_bytes());
        out.extend_from_slice(&self.kem_sig);

        out.extend_from_slice(&(self.kem_one_time.len() as u32).to_be_bytes());
        for ((id, _, sig), pair_bytes) in self.kem_one_time.iter().zip(&kem_one_time_bytes) {
            out.extend_from_slice(&id.to_be_bytes());
            push_len_prefixed(&mut out, pair_bytes);
            out.extend_from_slice(sig);
        }

        out.extend_from_slice(&self.next_id.to_be_bytes());

        // v4: each entry is the identifier of the last-resort KEM key the
        // handshake was made against, then the handshake's fingerprint.
        out.extend_from_slice(&(self.last_resort_seen.len() as u32).to_be_bytes());
        for (id, fp) in &self.last_resort_seen {
            out.extend_from_slice(&id.to_be_bytes());
            out.extend_from_slice(fp);
        }

        // v3: the retired prekeys a rotation keeps, each behind a presence byte.
        match &self.previous_signed_prekey {
            None => out.push(0x00),
            Some((secret, id, sig)) => {
                out.push(0x01);
                out.extend_from_slice(secret);
                out.extend_from_slice(&id.to_be_bytes());
                out.extend_from_slice(sig);
            }
        }
        match (&self.previous_kem, &previous_kem_bytes) {
            (Some((_, id, sig)), Some(pair_bytes)) => {
                out.push(0x01);
                push_len_prefixed(&mut out, pair_bytes);
                out.extend_from_slice(&id.to_be_bytes());
                out.extend_from_slice(sig);
            }
            _ => out.push(0x00),
        }
        debug_assert_eq!(
            out.len(),
            capacity,
            "the size arithmetic above drifted from the encoding"
        );
        Zeroizing::new(out)
    }

    /// Decode a store persisted by `to_bytes`. Canonical: trailing bytes
    /// past the last field are refused rather than ignored.
    ///
    /// **Every stored signature is verified under `identity_public`** before
    /// the store is returned (session-persistence.md, Prekey store, Semantic
    /// rules), and a store holding one that does not verify is refused as
    /// `Incoherent`. Two consequences a caller should know:
    ///
    /// - **It costs a signature verification per stored prekey**, paid once at
    ///   import and never on the wire. Measured on an M-series laptop in
    ///   release mode: about 216 microseconds for a store with no one-time
    ///   prekeys against about 24 before the rule, and about 23 milliseconds
    ///   against 5.4 for a store holding five hundred. Linear in a count the
    ///   format does not otherwise bound, which is why it is here and not in
    ///   `invariant`, where the fuzz targets would pay it after every step.
    /// - **A store a release before the rule wrote may now be refused.** See
    ///   `PrekeyStoreDecodeError::Incoherent` for which stores and why the
    ///   version is not bumped.
    ///
    /// **What it does not catch.** The rule binds the signatures, the identity
    /// key and the signed prekey's secret; it does not bind the KEM key pairs'
    /// secret material, which no stored value authenticates. A single flipped
    /// byte there still imports, and publishes a bundle whose signatures
    /// verify and whose handshake then fails inside the AEAD -- a worse ending
    /// than a refused bundle, because the peer commits before it finds out.
    /// The format survives more corruption than it did and not all of it.
    pub fn from_bytes(bytes: &[u8]) -> Result<PrekeyStore, PrekeyStoreDecodeError> {
        if bytes.is_empty() {
            return Err(PrekeyStoreDecodeError::TooShort);
        }
        let version = bytes[0];
        if version != PREKEY_STORE_VERSION
            && version != PREKEY_STORE_VERSION_V3
            && version != PREKEY_STORE_VERSION_V2
            && version != PREKEY_STORE_VERSION_V1
        {
            return Err(PrekeyStoreDecodeError::UnknownVersion);
        }
        let mut pos = 1;

        if bytes.len() < pos + 32 {
            return Err(PrekeyStoreDecodeError::TooShort);
        }
        let mut identity_public = [0u8; 32];
        identity_public.copy_from_slice(&bytes[pos..pos + 32]);
        pos += 32;

        if bytes.len() < pos + 32 {
            return Err(PrekeyStoreDecodeError::TooShort);
        }
        let mut signed_prekey_secret = [0u8; 32];
        signed_prekey_secret.copy_from_slice(&bytes[pos..pos + 32]);
        pos += 32;

        let Some(signed_prekey_id) = read_prekey_u32(bytes, pos) else {
            return Err(PrekeyStoreDecodeError::TooShort);
        };
        pos += 4;

        if bytes.len() < pos + 64 {
            return Err(PrekeyStoreDecodeError::TooShort);
        }
        let mut signed_prekey_sig = [0u8; 64];
        signed_prekey_sig.copy_from_slice(&bytes[pos..pos + 64]);
        pos += 64;

        let Some(one_time_count) = read_prekey_u32(bytes, pos) else {
            return Err(PrekeyStoreDecodeError::TooShort);
        };
        pos += 4;
        // Sized up front so the vector never grows as the loop pushes and never
        // strands an outgrown block of one-time secrets un-wiped (CR-15). The
        // count is untrusted, so the capacity is clamped to what the remaining
        // bytes could actually hold -- each entry is exactly 36 bytes on the
        // wire -- rather than trusting the header to size an allocation.
        let one_time_capacity = (one_time_count as usize).min(bytes.len().saturating_sub(pos) / 36);
        let mut one_time = Vec::with_capacity(one_time_capacity);
        for _ in 0..one_time_count {
            if bytes.len() < pos + 36 {
                return Err(PrekeyStoreDecodeError::TooShort);
            }
            let Some(id) = read_prekey_u32(bytes, pos) else {
                return Err(PrekeyStoreDecodeError::TooShort);
            };
            let mut secret = [0u8; 32];
            secret.copy_from_slice(&bytes[pos + 4..pos + 36]);
            one_time.push((id, secret));
            pos += 36;
        }

        let Some((kem_bytes, next_pos)) = take_len_prefixed(bytes, pos) else {
            return Err(PrekeyStoreDecodeError::TooShort);
        };
        let Ok(kem_keypair) = kem::KeyPair::from_bytes(kem_bytes) else {
            return Err(PrekeyStoreDecodeError::Malformed);
        };
        pos = next_pos;

        let Some(kem_id) = read_prekey_u32(bytes, pos) else {
            return Err(PrekeyStoreDecodeError::TooShort);
        };
        pos += 4;

        if bytes.len() < pos + 64 {
            return Err(PrekeyStoreDecodeError::TooShort);
        }
        let mut kem_sig = [0u8; 64];
        kem_sig.copy_from_slice(&bytes[pos..pos + 64]);
        pos += 64;

        let Some(kem_one_time_count) = read_prekey_u32(bytes, pos) else {
            return Err(PrekeyStoreDecodeError::TooShort);
        };
        pos += 4;
        // Sized up front like the curve vector above (CR-15). A KEM one-time
        // entry is at least 72 bytes on the wire (id, a length prefix, a
        // signature), so the untrusted count is clamped to what the remaining
        // bytes could hold rather than trusted to size the allocation.
        let kem_one_time_capacity =
            (kem_one_time_count as usize).min(bytes.len().saturating_sub(pos) / 72);
        let mut kem_one_time = Vec::with_capacity(kem_one_time_capacity);
        for _ in 0..kem_one_time_count {
            let Some(id) = read_prekey_u32(bytes, pos) else {
                return Err(PrekeyStoreDecodeError::TooShort);
            };
            pos += 4;
            let Some((pair_bytes, next_pos)) = take_len_prefixed(bytes, pos) else {
                return Err(PrekeyStoreDecodeError::TooShort);
            };
            let Ok(pair) = kem::KeyPair::from_bytes(pair_bytes) else {
                return Err(PrekeyStoreDecodeError::Malformed);
            };
            pos = next_pos;
            if bytes.len() < pos + 64 {
                return Err(PrekeyStoreDecodeError::TooShort);
            }
            let mut sig = [0u8; 64];
            sig.copy_from_slice(&bytes[pos..pos + 64]);
            pos += 64;
            kem_one_time.push((id, pair, sig));
        }

        let Some(next_id) = read_prekey_u32(bytes, pos) else {
            return Err(PrekeyStoreDecodeError::TooShort);
        };
        pos += 4;

        // A v1 store predates the fingerprints and simply has none.
        let mut last_resort_seen = Vec::new();
        if version != PREKEY_STORE_VERSION_V1 {
            let Some(seen_count) = read_prekey_u32(bytes, pos) else {
                return Err(PrekeyStoreDecodeError::TooShort);
            };
            pos += 4;
            // Refuse a count the encoder could never have written, before
            // trusting it to size anything. The bound is per key and no key's
            // entries exceed it in memory -- a handshake that would take one
            // past is refused rather than recorded -- so the ceiling here is
            // the bound times the number of keys the entries can name. A v4
            // entry names its own key and at most two can still decrypt, the
            // current one and the one the last rotation retired, so two full
            // budgets. An untagged v2 or v3 entry reads back under the current
            // key alone (see below), so such a file has one budget's worth at
            // most. Anything larger is corruption.
            //
            // This is only the cheap ceiling that stops a bogus count sizing
            // an allocation; the per-key bound itself is a clause of
            // `invariant`, which runs at the end of this function over the
            // decoded store, once each entry's tag is known. A v4 file
            // carrying 2048 entries all tagged with one key passes here and is
            // refused there.
            let seen_ceiling = if version == PREKEY_STORE_VERSION {
                MAX_LAST_RESORT_SEEN.saturating_mul(2)
            } else {
                MAX_LAST_RESORT_SEEN
            };
            if seen_count as usize > seen_ceiling {
                return Err(PrekeyStoreDecodeError::Malformed);
            }
            // A v4 entry carries the identifier of the last-resort KEM key it
            // was recorded under; a v2 or v3 entry is a bare fingerprint. The
            // untagged ones are tagged with the *current* key's identifier,
            // which is the conservative reading: the fingerprint alone decides
            // whether a handshake is a repeat (it covers the identifier), so
            // every replay the older store refused is still refused, and the
            // only effect of a wrong tag is that an entry made under the
            // retired key is dropped one rotation later than it need be.
            let tagged = version == PREKEY_STORE_VERSION;
            let entry_len = if tagged { 4 + 32 } else { 32 };
            last_resort_seen.reserve_exact(seen_count as usize);
            for _ in 0..seen_count {
                if bytes.len() < pos + entry_len {
                    return Err(PrekeyStoreDecodeError::TooShort);
                }
                let id = if tagged {
                    let Some(id) = read_prekey_u32(bytes, pos) else {
                        return Err(PrekeyStoreDecodeError::TooShort);
                    };
                    pos += 4;
                    id
                } else {
                    kem_id
                };
                let mut fp = [0u8; 32];
                fp.copy_from_slice(&bytes[pos..pos + 32]);
                pos += 32;
                last_resort_seen.push((id, fp));
            }
        }

        // A v1 or v2 store predates rotation and has retired nothing.
        let mut previous_signed_prekey = None;
        let mut previous_kem = None;
        if version == PREKEY_STORE_VERSION || version == PREKEY_STORE_VERSION_V3 {
            if bytes.len() < pos + 1 {
                return Err(PrekeyStoreDecodeError::TooShort);
            }
            match bytes[pos] {
                0x00 => pos += 1,
                0x01 => {
                    pos += 1;
                    if bytes.len() < pos + 32 + 4 + 64 {
                        return Err(PrekeyStoreDecodeError::TooShort);
                    }
                    let mut secret = [0u8; 32];
                    secret.copy_from_slice(&bytes[pos..pos + 32]);
                    pos += 32;
                    let Some(id) = read_prekey_u32(bytes, pos) else {
                        return Err(PrekeyStoreDecodeError::TooShort);
                    };
                    pos += 4;
                    let mut sig = [0u8; 64];
                    sig.copy_from_slice(&bytes[pos..pos + 64]);
                    pos += 64;
                    previous_signed_prekey = Some((secret, id, sig));
                }
                _ => return Err(PrekeyStoreDecodeError::Malformed),
            }
            if bytes.len() < pos + 1 {
                return Err(PrekeyStoreDecodeError::TooShort);
            }
            match bytes[pos] {
                0x00 => pos += 1,
                0x01 => {
                    pos += 1;
                    let Some((pair_bytes, next_pos)) = take_len_prefixed(bytes, pos) else {
                        return Err(PrekeyStoreDecodeError::TooShort);
                    };
                    let Ok(pair) = kem::KeyPair::from_bytes(pair_bytes) else {
                        return Err(PrekeyStoreDecodeError::Malformed);
                    };
                    pos = next_pos;
                    let Some(id) = read_prekey_u32(bytes, pos) else {
                        return Err(PrekeyStoreDecodeError::TooShort);
                    };
                    pos += 4;
                    if bytes.len() < pos + 64 {
                        return Err(PrekeyStoreDecodeError::TooShort);
                    }
                    let mut sig = [0u8; 64];
                    sig.copy_from_slice(&bytes[pos..pos + 64]);
                    pos += 64;
                    previous_kem = Some((pair, id, sig));
                }
                _ => return Err(PrekeyStoreDecodeError::Malformed),
            }
        }

        if pos != bytes.len() {
            return Err(PrekeyStoreDecodeError::Malformed);
        }

        let store = PrekeyStore {
            last_resort_seen,
            identity_public: dh::PublicKeyBytes::from_bytes(identity_public),
            signed_prekey_secret,
            signed_prekey_id,
            signed_prekey_sig,
            one_time,
            kem: kem_keypair,
            kem_id,
            kem_sig,
            kem_one_time,
            previous_signed_prekey,
            previous_kem,
            next_id,
        };

        // Canonicality backstop for the current version, the same one
        // `Session::import` applies (CR-18): if the decoded store does not
        // re-encode to the exact bytes it came from, they were not produced by
        // `to_bytes` and are refused. Skipped for v1 through v3, which
        // legitimately re-encode to v4 (they gain the fields the newer format
        // added, and the record its tags), so a re-encode comparison there
        // would reject every honest upgrade.
        //
        // For v4 as the decoder above stands, this is unreachable by
        // construction: every field is fixed-width or length-prefixed and
        // re-encoded exactly as read, the presence bytes admit only 0x00 and
        // 0x01, and trailing bytes are refused, so any byte string that decodes
        // re-encodes to itself. It is kept as insurance: a future field with
        // two encodings of one value would otherwise pass unnoticed, and the
        // check costs nothing to reason about. What it does cost is one full
        // re-encode per load, every held KEM key pair included, paid once at
        // restore and never on the wire.
        if version == PREKEY_STORE_VERSION && store.to_bytes().as_slice() != bytes {
            return Err(PrekeyStoreDecodeError::NonCanonical);
        }

        // The relations between fields that the reads above take on trust --
        // the identifier namespace and the record's shape -- checked last,
        // over the decoded store, by the same predicate the tests and the
        // fuzz targets assert after every operation. `invariant` says what
        // each clause prevents. A record entry under an unknown key, a
        // repeated fingerprint, a repeated or wound-back identifier: none
        // can come out of `to_bytes`, so all are refused as malformed.
        if !store.invariant() {
            return Err(PrekeyStoreDecodeError::Malformed);
        }

        // What the signatures authenticate, checked here and not in
        // `invariant` (session-persistence.md, Prekey store, Semantic rules,
        // "Every stored signature verifies under `identity_public`"). The five
        // rules above are cheap predicates over identifiers, tags and a key's
        // encoding, which
        // is why the tests and the fuzz targets can assert them after every
        // operation; this one costs a signature verification per stored
        // prekey. Reading is the moment worth paying it at, and the only
        // moment the bytes could have been corrupted.
        if !store.signatures_verify() {
            return Err(PrekeyStoreDecodeError::Incoherent);
        }

        Ok(store)
    }

    /// Whether every stored signature verifies under `identity_public`.
    ///
    /// The sixth semantic rule of the stored format, and the one the other five
    /// cannot reach: they relate identifiers and tags to each other, where this
    /// relates the stored signatures to the stored keys they are supposed to
    /// authenticate. A store failing it is refused by `from_bytes` as
    /// `Incoherent`, its own variant and not `Malformed`: see there for why,
    /// and for the compatibility break that refusal records.
    ///
    /// **Why it matters, given no secret is at risk.** `publish` copies these
    /// signatures verbatim into every bundle it emits, and nothing between here
    /// and there looks at them again. A single flipped byte in
    /// `signed_prekey_sig` -- offset 69 of a v4 store -- re-encodes canonically
    /// and satisfies `invariant`, so without this check the store restores
    /// cleanly and then publishes a bundle every initiator refuses with
    /// `BadSignedPrekeySignature`. The party sees nothing wrong; its peers see
    /// someone they cannot start a session with. That is a recovery defect, and
    /// the format's stated obligation is to survive corruption.
    ///
    /// The one-time *curve* prekeys are absent from this deliberately: they
    /// carry no signature, and `create_prekeys` says why only the KEM prekeys
    /// are signed individually.
    fn signatures_verify(&self) -> bool {
        let signed_ok = |secret: &[u8; 32], sig: &[u8; 64]| {
            let public = dh::PrivateKey::from_bytes(*secret).public_key();
            xeddsa::verify(&self.identity_public, &encode_ec(&public), sig).is_ok()
        };
        let kem_ok = |pair: &kem::KeyPair, sig: &[u8; 64]| {
            xeddsa::verify(&self.identity_public, &encode_kem(&pair.public_key()), sig).is_ok()
        };

        if !signed_ok(&self.signed_prekey_secret, &self.signed_prekey_sig) {
            return false;
        }
        if !kem_ok(&self.kem, &self.kem_sig) {
            return false;
        }
        if self
            .kem_one_time
            .iter()
            .any(|(_, pair, sig)| !kem_ok(pair, sig))
        {
            return false;
        }
        if let Some((secret, _, sig)) = &self.previous_signed_prekey {
            if !signed_ok(secret, sig) {
                return false;
            }
        }
        if let Some((pair, _, sig)) = &self.previous_kem {
            if !kem_ok(pair, sig) {
                return false;
            }
        }
        true
    }

    /// Whether this store is one `create_prekeys` builds and every operation
    /// on it preserves: the identifier namespace and the replay record's
    /// shape, which no field-by-field read can see.
    ///
    /// `from_bytes` refuses a store for which this is false (`Malformed`),
    /// last, once the fields have decoded; the tests and the fuzz targets
    /// assert it after every operation, so that it is checked as an inductive
    /// invariant rather than trusted at one point. The clauses:
    ///
    /// - **Every identifier is below `next_id`.** `next_id` only climbs and
    ///   is what every identifier was handed out from, so one at or past it
    ///   is corruption or a counter wound back, and the next key handed out
    ///   would collide with a live one: a corrupted `next_id` poisons every
    ///   future bundle, and persists canonically.
    /// - **No identifier is the absent-identifier sentinel** (`ABSENT_ID`,
    ///   zero). `create_prekeys` numbers from one. A one-time prekey under
    ///   zero could never be named by an initial message, which reads zero
    ///   as "none", so it would sit in the store unconsumable.
    /// - **Every identifier is distinct**: the signed prekey's, the
    ///   last-resort KEM key's, the two a rotation retired, and each one-time
    ///   key's of either kind. The store finds keys by their *first* match,
    ///   so a repeated one-time identifier lets a replayed initial message be
    ///   served twice (the note on `next_id`); a retired identifier equal to
    ///   the live one has the next `rotate_kem` drop the live key's record
    ///   entries, after which every replay they refused is accepted; and a
    ///   one-time KEM identifier equal to a last-resort one is looked up on
    ///   the last-resort path and never consumed. One counter numbers them
    ///   all, so distinctness across every kind is what the constructor
    ///   establishes, not only within each.
    /// - **Every record entry is tagged with a key that can still decrypt**
    ///   -- the current last-resort key or the retired one -- **no key has
    ///   more than `MAX_LAST_RESORT_SEEN` of them, and no fingerprint appears
    ///   twice.** The bound is counted per key, not over the record as a
    ///   whole, which is what the record itself is bounded by: two live keys
    ///   means the record holds at most two budgets.
    ///   `establish_responder` refuses the handshake that would take a key
    ///   past its budget, and the repeat of one already in the record, before
    ///   either could be recorded; `rotate_kem` drops a key's entries when it
    ///   wipes the key; and `to_bytes` never writes anything else. A file
    ///   whose entries exceed one key's budget is refused here, which is the
    ///   only place the tags are available to count by.
    /// - **The identity key is canonical** (session-persistence.md, Stored
    ///   curve public keys). Every bundle the store publishes carries it, and
    ///   a peer's bundle decoder refuses any other spelling. `create_prekeys`
    ///   takes it from the identity's secret, so X25519 computed it, and no
    ///   operation changes it.
    pub fn invariant(&self) -> bool {
        if !is_canonical_key(&self.identity_public) {
            return false;
        }
        let previous_signed_id = self.previous_signed_prekey.as_ref().map(|(_, id, _)| *id);
        let previous_kem_id = self.previous_kem.as_ref().map(|(_, id, _)| *id);

        let mut ids: Vec<u32> = vec![self.signed_prekey_id, self.kem_id];
        ids.extend(previous_signed_id);
        ids.extend(previous_kem_id);
        ids.extend(self.one_time.iter().map(|(id, _)| *id));
        ids.extend(self.kem_one_time.iter().map(|(id, _, _)| *id));
        let mut distinct = std::collections::HashSet::with_capacity(ids.len());
        for id in &ids {
            if *id == ABSENT_ID || *id >= self.next_id || !distinct.insert(*id) {
                return false;
            }
        }

        // Counted per key as the entries are walked, rather than by a scan
        // per key: the two live keys are the only tags a valid record carries,
        // so two counters cover it, and an entry naming anything else is
        // refused on sight.
        let mut current_seen: usize = 0;
        let mut previous_seen: usize = 0;
        let mut fingerprints =
            std::collections::HashSet::with_capacity(self.last_resort_seen.len());
        for (id, fp) in &self.last_resort_seen {
            if *id == self.kem_id {
                current_seen += 1;
            } else if Some(*id) == previous_kem_id {
                previous_seen += 1;
            } else {
                return false;
            }
            if !fingerprints.insert(*fp) {
                return false;
            }
        }
        if current_seen > MAX_LAST_RESORT_SEEN || previous_seen > MAX_LAST_RESORT_SEEN {
            return false;
        }
        true
    }
}

/// This module's own persistence-format version for `PrekeyStore::to_bytes`/
/// `from_bytes`, separate from any on-the-wire message version.
///
/// The version `to_bytes` writes. `from_bytes` also accepts the three earlier
/// formats so an older store still restores: `PREKEY_STORE_VERSION_V3`, whose
/// last-resort record entries are bare fingerprints with no key identifier
/// (they read back tagged with the current last-resort key; `from_bytes` says
/// why that is safe); `PREKEY_STORE_VERSION_V2`, which additionally lacks the
/// retired-prekey fields (it reads back with nothing retired); and
/// `PREKEY_STORE_VERSION_V1`, which additionally lacks the last-resort record
/// (it reads back with none remembered). Each is the honest answer for a
/// store written before those fields existed.
const PREKEY_STORE_VERSION: u8 = 0x04;
/// The format before the replay record was tagged by key: each entry is a
/// bare fingerprint, and the record was a window evicted oldest-first.
const PREKEY_STORE_VERSION_V3: u8 = 0x03;
/// The format before prekey rotation: v3 without the
/// two retired-prekey fields. Reads back with nothing retired.
const PREKEY_STORE_VERSION_V2: u8 = 0x02;
/// The format before last-resort replay marking.
const PREKEY_STORE_VERSION_V1: u8 = 0x01;

/// A `PrekeyStore::to_bytes`/`from_bytes` failure. As with `Session`'s own
/// `SessionDecodeError`, the threat model is corruption and version skew,
/// not a hostile peer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum PrekeyStoreDecodeError {
    UnknownVersion,
    TooShort,
    Malformed,
    /// The bytes decoded, and re-encoding the result did not reproduce them.
    ///
    /// The same backstop `Session::import` carries (CR-18): a current-version
    /// (v4) store whose bytes are not the encoding of what they decode to was
    /// not produced by `to_bytes`, and is refused rather than accepted under a
    /// second spelling. Only checked for v4; v1 through v3 legitimately
    /// re-encode to the current version and so are exempt.
    NonCanonical,
    /// The bytes decoded, keep every structural rule, and hold a signature
    /// that does not verify under `identity_public`.
    ///
    /// Distinct from `Malformed` for the reason `Session::import` gives
    /// `Inconsistent`: a store that is well-formed and canonical but cannot go
    /// on is the one case a storage layer could plausibly have written itself,
    /// and a caller that can tell it from corruption can act on it -- every
    /// secret in the file is still where it was, to be read out by hand if it
    /// matters, where a corrupt file's may not be.
    ///
    /// **This refusal is a compatibility break, and a deliberate one.** A
    /// release before this rule existed accepted an `Identity` other than the
    /// store's in `replenish`, `rotate_signed_prekey` and `rotate_kem`, and
    /// wrote the result at this same version, so a v4 store one of those
    /// releases restores can be refused here. It was never usable: every
    /// bundle it publishes is refused by every initiator. Refusing it at
    /// import is therefore not a loss of function but an earlier and clearer
    /// report of one, which is why the version is not bumped and why this
    /// variant exists rather than the case folding into `Malformed`.
    Incoherent,
}

fn read_prekey_u32(bytes: &[u8], pos: usize) -> Option<u32> {
    if bytes.len() < pos + 4 {
        return None;
    }
    let mut b = [0u8; 4];
    b.copy_from_slice(&bytes[pos..pos + 4]);
    Some(u32::from_be_bytes(b))
}

/// What can go wrong establishing or advancing a session.
///
/// `#[non_exhaustive]` because this crate is pre-1.0 and the receive and
/// establish paths are still gaining refusals (CR-27): a consumer must have a
/// wildcard arm, so that adding a variant is not a breaking change.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum Error {
    /// The composition refused: either ratchet may be the reason, and the
    /// variant carries which.
    Triple(tacenta_triple::TripleError),
    /// A check on the handshake's keys refused, and the [`SessionError`] says
    /// which. Either a prekey signature in the bundle did not verify
    /// (`BadSignedPrekeySignature`, `BadKemPrekeySignature`), or a
    /// Diffie-Hellman agreement was not contributory
    /// (`NonContributoryAgreement`).
    ///
    /// The second can come from any receive, not only from establishment.
    /// `decrypt` checks the ratchet public key on every incoming message and
    /// refuses a low-order one with this variant, before the message is
    /// authenticated.
    Handshake(SessionError),
    /// A KEM public key or ciphertext was malformed.
    Kem,
    /// A message did not decode.
    Decode(DecodeError),
    /// A curve public key on the wire was not a recognised encoding.
    BadEncoding,
    /// A bundle's one-time prekey and its identifier disagree on presence: one
    /// is present and the other absent. A directory that serves such a bundle
    /// would make the two sides derive different shared secrets, so it is
    /// refused here rather than left to surface as an opaque AEAD failure that
    /// looks like a network fault (CR-17).
    InconsistentBundle,
    /// The bundle's identity key is not the one the caller expected. Pinning is
    /// an argument of [`establish_initiator_for`], so a substituted bundle from
    /// the directory is refused during establishment rather than by a
    /// `peer_identity()` comparison the caller must remember to make (CR-27).
    UnexpectedIdentity,
    /// An identifier named a prekey the store does not hold.
    UnknownPrekeyId,
    /// The AEAD did not authenticate.
    Aead,
    /// An initial message arrived on an established session and is not a repeat
    /// of the one that established it: the session is not a responder's, or
    /// the message's `ephemeral` or `identity` is not the session's. Opening a
    /// session is `establish_responder`'s job, and doing it here would discard
    /// this one.
    NotARepeatedInitial,
    /// A last-resort handshake this store has already accepted arrived again.
    ///
    /// Distinct from `NotARepeatedInitial`, which is about a *session* that
    /// already exists. This one fires before any session does: the initial
    /// message names the reusable last-resort KEM key, and its fingerprint
    /// matches one already spent. See `last_resort_seen`.
    ReplayedLastResort,
    /// A last-resort handshake this store has not seen arrived while its
    /// replay record is full, and was refused rather than recorded.
    ///
    /// The record holds at most `MAX_LAST_RESORT_SEEN` entries **for each**
    /// last-resort KEM key that can still decrypt -- the current one and the
    /// one a rotation retired -- and it never evicts: eviction was what let
    /// anyone holding the public bundle forget a victim's fingerprint by
    /// completing enough handshakes of their own. So the handshake that would
    /// take its key past that key's budget is refused before anything is
    /// decrypted or changed, and the store is exactly as it was. It says
    /// nothing about the other key, which keeps its own budget. Only the
    /// last-resort path is affected; an initial message naming a one-time KEM
    /// prekey never consults the record. Recovery is the operator's:
    /// `replenish` one-time KEM prekeys so that first contacts stop landing
    /// here, and `rotate_kem`, which opens a key with an empty budget and is
    /// what every bundle handed out afterwards names, so one rotation is
    /// enough. See `last_resort_seen`.
    LastResortRecordFull,
    /// The post-quantum key agreement (the Braid) reached its terminal failure
    /// state, so no further post-quantum epoch can be agreed on this session.
    ///
    /// The Braid's own contract is that failure is terminal and the session is
    /// abandoned. A session that did not check would carry on after a failure
    /// with an epoch-0 header -- either still encrypting on the epoch-0 chain,
    /// with the post-quantum post-compromise property gone and nothing telling
    /// anyone, or wedged with an opaque `NoChain`. Instead
    /// `encrypt` refuses, `decrypt` refuses everything after the message that
    /// revealed the failure (that message's plaintext is still returned: it
    /// authenticated, and dropping it would lose real data), and
    /// `agreement_failed` reports the state. Re-establish the session.
    ///
    /// **Persist on this error too.** `encrypt` commits the Braid's terminal
    /// state before returning `AgreementFailed`, so that the failure is
    /// terminal in memory; it is terminal across a restart only if the
    /// session is persisted after the error, which the ordinary "persist
    /// after `encrypt` returns `Ok`" discipline does not cover. A caller that
    /// persists only on success will find `agreement_failed()` false after a
    /// restart and the next `send` may succeed, which is the state before the
    /// failing call, not a resurrection of the agreement.
    AgreementFailed,
}

/// One established session: the ratchet state, the private key behind the current
/// ratchet public key, the associated data binding both identities, and, until
/// the first message is sent, the material for the initial message.
pub struct Session {
    /// Both message ratchets.
    triple: tacenta_triple::State,
    /// The agreement beneath the post-quantum ratchet. Driven by the session
    /// because the Triple Ratchet takes its epoch and output as arguments
    /// rather than owning it.
    braid: tacenta_braid::Braid,
    ratchet_private: dh::PrivateKey,
    identity_ad: Vec<u8>,
    our_identity_public: dh::PublicKeyBytes,
    peer_identity_public: dh::PublicKeyBytes,
    /// The initial message this session has still to send, if it is an
    /// initiator's and the peer has not yet answered.
    pending_initial: Option<PendingInitial>,
    /// The initiator ephemeral this session was established from, if it is a
    /// responder's. It is what lets a *repeated* initial message be recognised
    /// as belonging to this session rather than opening another one.
    established_ephemeral: Option<Vec<u8>>,
}

/// The externally observable state of a session: only public keys and counters,
/// never internal or private state. Used to detect a changed peer identity and to
/// report progress.
pub struct PublicState {
    pub peer_identity: dh::PublicKeyBytes,
    pub our_ratchet_public: [u8; 32],
    pub sent: u32,
    pub received: u32,
}

/// The composite header: the Triple Ratchet's own, plus the agreement's message.
fn composite_of(h: &tacenta_triple::Header, m: &tacenta_braid::Msg) -> Composite {
    Composite {
        dh: h.dr.dh,
        pn: h.dr.pn,
        n: h.dr.n,
        pq_epoch: h.epoch,
        pq_n: h.pq_n,
        ag_epoch: m.epoch,
        ag_type: agreement_type_of(m.ty),
        ag_chunk: m.data.as_ref().map(|c| Codeword {
            index: c.index,
            data: c.data,
        }),
    }
}

/// And back, for a header that arrived.
fn msg_of(c: &Composite) -> tacenta_braid::Msg {
    tacenta_braid::Msg {
        epoch: c.ag_epoch,
        ty: msg_type_of(c.ag_type),
        data: c.ag_chunk.as_ref().map(|w| tacenta_erasure::Chunk {
            index: w.index,
            data: w.data,
        }),
    }
}

/// The Triple Ratchet's header, reconstructed from what arrived.
fn triple_header_of(c: &Composite) -> tacenta_triple::Header {
    tacenta_triple::Header {
        dr: ratchet::Header {
            dh: c.dh,
            pn: c.pn,
            n: c.n,
        },
        epoch: c.pq_epoch,
        pq_n: c.pq_n,
    }
}

fn agreement_type_of(t: tacenta_braid::MsgType) -> AgreementType {
    match t {
        tacenta_braid::MsgType::None => AgreementType::None,
        tacenta_braid::MsgType::Hdr => AgreementType::Hdr,
        tacenta_braid::MsgType::Ek => AgreementType::Ek,
        tacenta_braid::MsgType::EkCt1Ack => AgreementType::EkCt1Ack,
        tacenta_braid::MsgType::Ct1 => AgreementType::Ct1,
        tacenta_braid::MsgType::Ct2 => AgreementType::Ct2,
    }
}

fn msg_type_of(t: AgreementType) -> tacenta_braid::MsgType {
    match t {
        AgreementType::None => tacenta_braid::MsgType::None,
        AgreementType::Hdr => tacenta_braid::MsgType::Hdr,
        AgreementType::Ek => tacenta_braid::MsgType::Ek,
        AgreementType::EkCt1Ack => tacenta_braid::MsgType::EkCt1Ack,
        AgreementType::Ct1 => tacenta_braid::MsgType::Ct1,
        AgreementType::Ct2 => tacenta_braid::MsgType::Ct2,
    }
}

impl Session {
    /// The peer's long-term identity key. An application compares this to the
    /// value it remembers for a contact to detect an identity change.
    pub fn peer_identity(&self) -> dh::PublicKeyBytes {
        self.peer_identity_public
    }

    /// The externally observable state.
    pub fn public_state(&self) -> PublicState {
        PublicState {
            peer_identity: self.peer_identity_public,
            our_ratchet_public: self.triple.sending_public(),
            sent: self.triple.send_count(),
            received: self.triple.receive_count(),
        }
    }
}

struct PendingInitial {
    ephemeral_public: dh::PublicKeyBytes,
    kem_ciphertext: Vec<u8>,
    signed_prekey_id: u32,
    one_time_prekey_id: u32,
    kem_prekey_id: u32,
}

/// Associated data binding both identities, initiator first so both sides agree.
fn identity_ad(initiator: &dh::PublicKeyBytes, responder: &dh::PublicKeyBytes) -> Vec<u8> {
    associated_data(&encode_ec(initiator), &encode_ec(responder))
}

/// Establish a session as the initiator, from the peer's published bundle. The
/// session is returned pending: the first `encrypt` produces the initial message.
///
/// **This trusts whatever identity the bundle carries.** A directory that
/// substitutes a bundle yields a session to that directory unless the caller
/// compares [`Session::peer_identity`] afterwards. When the caller already
/// knows which identity it means to reach -- the usual case, a contact whose
/// key it has pinned -- prefer [`establish_initiator_for`], which folds that
/// comparison into establishment so it cannot be forgotten (CR-27).
pub fn establish_initiator<R: RngCore + CryptoRng>(
    our_identity: &Identity,
    their_bundle: &PublishedBundle,
    rng: &mut R,
) -> Result<Session, Error> {
    // No identity to pin against, so pin against the one the bundle carries:
    // this is exactly the trusting behaviour above, expressed as a delegation
    // rather than duplicated.
    let expected = their_bundle.bundle.identity_key;
    establish_initiator_for(our_identity, their_bundle, &expected, rng)
}

/// Establish a session as the initiator against a **known** peer identity.
///
/// Identical to [`establish_initiator`] except that the bundle's identity key
/// must equal `expected_identity`; a mismatch is [`Error::UnexpectedIdentity`]
/// and no session is created. This is the pinning most callers want: the
/// comparison a substituted bundle would otherwise slip past becomes a
/// precondition of establishment rather than a follow-up the caller must
/// remember (CR-27).
pub fn establish_initiator_for<R: RngCore + CryptoRng>(
    our_identity: &Identity,
    their_bundle: &PublishedBundle,
    expected_identity: &dh::PublicKeyBytes,
    rng: &mut R,
) -> Result<Session, Error> {
    let bundle = &their_bundle.bundle;
    // Pin the identity before any work: a substituted bundle is refused here,
    // not discovered later through `peer_identity()`.
    if bundle.identity_key != *expected_identity {
        return Err(Error::UnexpectedIdentity);
    }
    // The one-time prekey and its identifier must agree on presence. A
    // directory serving one without the other makes the two sides fold a
    // different fourth agreement, so they derive different shared secrets and
    // the handshake wedges silently; refused here as a malformed bundle rather
    // than left to look like a network fault (CR-17).
    if bundle.one_time_prekey.is_some() != (their_bundle.one_time_prekey_id != ABSENT_ID) {
        return Err(Error::InconsistentBundle);
    }
    // Every curve public key in the bundle is its canonical encoding
    // (session-establishment.md, Sending the initial message). `decode_bundle`
    // already refuses any other, but a `PublishedBundle` can be built without
    // it, and the session stores the identity key and the signed prekey:
    // accepted re-spelled, they would make a session its own reader refuses
    // (session-persistence.md, Stored curve public keys).
    let one_time_canonical = match &bundle.one_time_prekey {
        None => true,
        Some(k) => is_canonical_key(k),
    };
    if !is_canonical_key(&bundle.identity_key)
        || !is_canonical_key(&bundle.signed_prekey)
        || !one_time_canonical
    {
        return Err(Error::BadEncoding);
    }
    // PQXDH §3.3 verifies the bundle's signatures before anything else, and
    // so does this, rather than spending a KEM encapsulation against a prekey
    // nobody has vouched for. `initiator_shared_secret` still verifies for its
    // own callers; the second check is cheap beside the encapsulation.
    super::verify_bundle(bundle).map_err(Error::Handshake)?;
    let ephemeral = dh::PrivateKey::from_bytes(random_secret(rng));
    // Wiped on the way out: the encapsulated secret is one of the values the
    // specifications require deleting once the shared secret is derived.
    let (kem_ciphertext, ss) = kem::encapsulate(&bundle.kem_prekey, rng).map_err(|_| Error::Kem)?;
    let ss = Zeroizing::new(ss);
    // `SK` is the root of every key this session will ever derive, so it is
    // wrapped like `ss` beside it.
    let sk = Zeroizing::new(
        initiator_shared_secret(&our_identity.dh_key(), &ephemeral, bundle, &ss)
            .map_err(Error::Handshake)?,
    );

    let ratchet_private = dh::PrivateKey::from_bytes(random_secret(rng));
    let peer_signed_prekey = bundle.signed_prekey;
    // Wiped on the way out: this is the `KDF_RK` input the specifications
    // require deleting once the next root key is derived (CR-08, key-deletion.md),
    // held like every other Diffie-Hellman output in this layer.
    let dh_out = Zeroizing::new(
        ratchet_private
            .agree(&peer_signed_prekey)
            .ok_or(Error::Handshake(SessionError::NonContributoryAgreement))?,
    );
    // §7.1: the handshake secret is expanded into one secret per ratchet, which
    // `init_sender` does internally, and the agreement's authenticator is
    // initialised from the PQXDH output itself.
    let triple = tacenta_triple::State::init_sender(
        &sk[..],
        *ratchet_private.public_key().as_bytes(),
        *peer_signed_prekey.as_bytes(),
        &dh_out,
        ratchet::LabelSet::Tacenta,
    );
    let braid = tacenta_braid::Braid::initiator(&sk[..]);

    Ok(Session {
        triple,
        braid,
        ratchet_private,
        identity_ad: identity_ad(&our_identity.public(), &bundle.identity_key),
        our_identity_public: our_identity.public(),
        peer_identity_public: bundle.identity_key,
        pending_initial: Some(PendingInitial {
            ephemeral_public: ephemeral.public_key(),
            kem_ciphertext,
            signed_prekey_id: their_bundle.signed_prekey_id,
            one_time_prekey_id: their_bundle.one_time_prekey_id,
            kem_prekey_id: their_bundle.kem_prekey_id,
        }),
        established_ephemeral: None,
    })
}

/// Establish a session as the responder, from an incoming initial message. The
/// message carries the first ratchet message, so this returns the session and the
/// first plaintext together.
///
/// On success this has also *mutated `our_prekeys`*: the one-time prekeys the
/// message named are deleted and, on the last-resort path, its fingerprint is
/// recorded. A storage layer must persist the returned session and then the
/// store, in that order and ideally atomically; `Session::export` spells out
/// what a crash between the two costs. On any refusal the store is untouched,
/// including the two refusals that precede decryption on the last-resort path
/// (`ReplayedLastResort` and `LastResortRecordFull`).
pub fn establish_responder<R: RngCore + CryptoRng>(
    our_identity: &Identity,
    our_prekeys: &mut PrekeyStore,
    initial_message: &[u8],
    rng: &mut R,
) -> Result<(Session, Vec<u8>), Error> {
    let decoded = decode_initial(initial_message).map_err(Error::Decode)?;

    // The current signed prekey, or the one a rotation just retired: a bundle
    // fetched before `rotate_signed_prekey` names the latter, and it is
    // honoured for one rotation (see that method).
    // Wrapped: this copy lives for the whole handshake, and a bare `[u8; 32]`
    // would outlive its use unwiped. The `from_bytes` calls below take a
    // transient copy each, which is the accepted class.
    // A guarded `match` rather than a let-chain: the workspace promises Rust
    // 1.87, and let-chains are stable only from 1.88.
    let signed_prekey_secret: Zeroizing<[u8; 32]> = Zeroizing::new(
        if decoded.signed_prekey_id == our_prekeys.signed_prekey_id {
            our_prekeys.signed_prekey_secret
        } else {
            match &our_prekeys.previous_signed_prekey {
                Some((secret, id, _)) if *id == decoded.signed_prekey_id => *secret,
                _ => return Err(Error::UnknownPrekeyId),
            }
        },
    );

    // **The one-time prekeys named here are read, not deleted.**
    //
    // Nothing has authenticated this message yet. PQXDH deletes a one-time
    // prekey's private half after the initial ciphertext decrypts, and this
    // repository's own key-deletion page says the same. Deleting on the way in
    // meant anyone who fetched a published bundle could burn one-time keys with
    // a message they could not have written: it rejects legitimate initial
    // messages already in flight, drains the store, and forces every later
    // peer onto the reusable last-resort KEM key, which is the one that carries
    // no one-time forward secrecy.
    //
    // Deletion happens at the end of this function, once and only once the
    // ciphertext has authenticated.
    // The last-resort path has no self-defence: the key is reusable, so unlike
    // a one-time prekey it is still there on the second delivery. Checked here,
    // before the KEM decapsulation, because the fingerprint is over public
    // bytes and there is no reason to do the expensive work for a message that
    // is already spent. Recorded at the end, once authenticated, on the same
    // discipline as the deletions.
    // The retired last-resort key is a last-resort key still: reusable, so
    // fingerprinted and remembered on exactly the same terms as the current.
    let previous_kem = our_prekeys
        .previous_kem
        .as_ref()
        .filter(|(_, id, _)| *id == decoded.kem_prekey_id)
        .map(|(pair, _, _)| pair);
    let last_resort = decoded.kem_prekey_id == our_prekeys.kem_id || previous_kem.is_some();
    let fingerprint = last_resort.then(|| last_resort_fingerprint(&decoded));
    if let Some(fp) = &fingerprint {
        // The fingerprint alone identifies the handshake -- it covers the KEM
        // prekey identifier -- so the tag on each entry plays no part here; it
        // exists for `rotate_kem` to prune by. Matching on the fingerprint
        // alone is also what lets a store upgraded from an untagged format
        // keep refusing everything it refused before.
        if our_prekeys
            .last_resort_seen
            .iter()
            .any(|(_, seen)| seen == fp)
        {
            return Err(Error::ReplayedLastResort);
        }
        // Fail closed on a spent budget. Recording this handshake at the end
        // would take its own key past `MAX_LAST_RESORT_SEEN`, and the record
        // never evicts: evicting oldest-first let anyone with the public
        // bundle push a victim's fingerprint out with a thousand cheap
        // handshakes of their own and then replay the victim's message (the
        // field's note says more). Refused here, before decapsulation, so the
        // store is untouched and no plaintext is produced for a message that
        // could not be remembered.
        //
        // Counted over the entries tagged with the key *this* handshake names,
        // not over the whole record. The two live keys hold separate budgets,
        // so a retired key that a burst filled before the last rotation cannot
        // refuse handshakes against the current one -- which is what makes
        // `rotate_kem` relief on the first rotation rather than the second.
        if our_prekeys.last_resort_seen_for(decoded.kem_prekey_id) >= MAX_LAST_RESORT_SEEN {
            return Err(Error::LastResortRecordFull);
        }
    }

    let kem_one_time = if last_resort {
        None
    } else {
        Some(
            our_prekeys
                .peek_one_time_kem(decoded.kem_prekey_id)
                .ok_or(Error::UnknownPrekeyId)?,
        )
    };

    let initiator_identity = decode_ec(&decoded.identity).ok_or(Error::BadEncoding)?;
    let initiator_ephemeral = decode_ec(&decoded.ephemeral).ok_or(Error::BadEncoding)?;

    // Read, not deleted, for the reason given above the KEM prekey.
    let one_time = if decoded.one_time_prekey_id == ABSENT_ID {
        None
    } else {
        Some(
            our_prekeys
                .peek_one_time(decoded.one_time_prekey_id)
                .ok_or(Error::UnknownPrekeyId)?,
        )
    };
    let one_time_key = one_time.as_ref().map(|s| dh::PrivateKey::from_bytes(**s));

    let kem_key = kem_one_time.or(previous_kem).unwrap_or(&our_prekeys.kem);
    // Wiped on the way out, for the same reason as the initiator's.
    let ss =
        Zeroizing::new(kem::decapsulate(kem_key, &decoded.kem_ciphertext).map_err(|_| Error::Kem)?);
    let signed_prekey = dh::PrivateKey::from_bytes(*signed_prekey_secret);
    // Wrapped for the same reason as the initiator's.
    let sk = Zeroizing::new(
        responder_shared_secret(
            &our_identity.dh_key(),
            &signed_prekey,
            one_time_key.as_ref(),
            &initiator_identity,
            &initiator_ephemeral,
            &ss,
        )
        .map_err(Error::Handshake)?,
    );

    let triple = tacenta_triple::State::init_receiver(
        &sk[..],
        *signed_prekey.public_key().as_bytes(),
        ratchet::LabelSet::Tacenta,
    );
    let braid = tacenta_braid::Braid::responder(&sk[..]);
    let mut session = Session {
        triple,
        braid,
        ratchet_private: dh::PrivateKey::from_bytes(*signed_prekey_secret),
        identity_ad: identity_ad(&initiator_identity, &our_identity.public()),
        our_identity_public: our_identity.public(),
        peer_identity_public: initiator_identity,
        pending_initial: None,
        established_ephemeral: Some(decoded.ephemeral.clone()),
    };

    // This authenticates the initial ciphertext. Nothing above it may have
    // changed the store, and nothing below it runs unless this succeeded.
    let plaintext = session.decrypt_ratchet(&decoded.message, rng)?;

    // Authenticated, so the one-time keys this message consumed are now spent
    // and their private halves must not outlive the use. This is their
    // deletion, and it is the only place it happens.
    if !last_resort {
        our_prekeys.take_one_time_kem(decoded.kem_prekey_id);
    }
    if decoded.one_time_prekey_id != ABSENT_ID {
        our_prekeys.take_one_time(decoded.one_time_prekey_id);
    }
    // A last-resort handshake cannot be deleted, so it is remembered instead,
    // tagged with the key it was made against so that `rotate_kem` can drop
    // it when that key is wiped. Room for it was checked before decryption;
    // nothing is evicted to make it.
    if let Some(fp) = fingerprint {
        debug_assert!(
            our_prekeys.last_resort_seen_for(decoded.kem_prekey_id) < MAX_LAST_RESORT_SEEN,
            "the record-full refusal must run before anything is recorded"
        );
        our_prekeys
            .last_resort_seen
            .push((decoded.kem_prekey_id, fp));
    }
    Ok((session, plaintext))
}

impl Session {
    /// Whether the post-quantum key agreement has reached its terminal failure
    /// state. Once true, `encrypt` and `decrypt` return
    /// [`Error::AgreementFailed`]; the session must be re-established.
    pub fn agreement_failed(&self) -> bool {
        self.braid.failed()
    }

    /// Encrypt a message.
    ///
    /// An initiator prepends the initial (prekey) message to **every** message
    /// until the peer answers, as the Double Ratchet specification recommends:
    /// an initial message sent only once can be lost or reordered, leaving the
    /// peer with no session and every later message undecryptable. The
    /// conformance suite exercises this by asking a responder to read a third
    /// message first.
    pub fn encrypt<R: RngCore + CryptoRng>(
        &mut self,
        plaintext: &[u8],
        rng: &mut R,
    ) -> Result<Vec<u8>, Error> {
        // A failed agreement is terminal: refuse rather than send an epoch-0
        // header on a session whose post-quantum ratchet can no longer advance.
        if self.braid.failed() {
            return Err(Error::AgreementFailed);
        }

        // The agreement runs **first**, because the Triple Ratchet takes its
        // epoch and output as arguments, and commits **last**, because the
        // ratchet can fail and the agreement's *state* cannot be lost.
        // Committing it here and failing below would advance the agreement for
        // a message never sent, the same rule `Triple::send` follows one level
        // down.
        let (ag_msg, sending_epoch, output, braid_next) = self.braid.send(rng);

        // `send` itself can reach the terminal state (an encapsulation error).
        // Commit that state so every later call refuses too, and say so, rather
        // than emitting a message at epoch 0.
        if braid_next.failed() {
            self.braid = braid_next;
            return Err(Error::AgreementFailed);
        }

        let spqr_output = output
            .as_ref()
            .map(|o| tacenta_spqr::Output::new(o.key_epoch, o.key));

        let mut candidate = self.triple.clone();
        let (header, mk) = candidate
            .send(sending_epoch, spqr_output.as_ref())
            .map_err(Error::Triple)?;

        let composite = composite_of(&header, &ag_msg);
        // Wiped on the way out, as on the receive side.
        let mk = Zeroizing::new(mk);
        let keys = Zeroizing::new(ratchet::message_keys(&mk, ratchet::LabelSet::Tacenta));
        let (enc, mac, iv) = &*keys;
        let ad = concat_ad(&self.identity_ad, &composite);
        let ciphertext = aead::encrypt(enc, mac, iv, plaintext, &ad);
        let ratchet_message = encode_message(&composite, &ciphertext);

        // Nothing below here can fail, so this is where both halves commit.
        self.triple = candidate;
        self.braid = braid_next;

        match self.pending_initial.as_ref() {
            None => Ok(ratchet_message),
            Some(p) => Ok(encode_initial(
                &encode_ec(&self.our_identity_public),
                &encode_ec(&p.ephemeral_public),
                &p.kem_ciphertext,
                p.signed_prekey_id,
                p.one_time_prekey_id,
                p.kem_prekey_id,
                &ratchet_message,
            )),
        }
    }

    /// Decrypt a message on an established session.
    ///
    /// Accepts either kind. A ratchet message is decrypted directly. An initial
    /// message is accepted only when it is a *repeat* of the one that
    /// established this session, which an initiator sends until it hears back:
    /// the wrapper is stripped and the ratchet message inside it decrypted. An
    /// initial message from a different establishment is refused here, because
    /// opening a session is `establish_responder`'s job and doing it
    /// inside an existing one would discard the session in place.
    ///
    /// A repeat is recognised by the two wrapper fields the session holds
    /// (session-establishment.md, Receiving the initial message): `ephemeral`
    /// must equal `established_ephemeral` and `identity` must equal the
    /// `EncodeEC` of the peer's identity key, each byte for byte. The decoder
    /// has already refused a re-spelled key in either field, and a key has one
    /// canonical encoding, so a genuine repeat matches and nothing else that
    /// names another key does. `kem_ciphertext` and the three identifiers are
    /// not compared, since the session keeps none of them, and nothing reads
    /// them: the inner message authenticates under this session's keys and
    /// associated data, and the ratchet refuses one it has already accepted.
    pub fn decrypt<R: RngCore + CryptoRng>(
        &mut self,
        message: &[u8],
        rng: &mut R,
    ) -> Result<Vec<u8>, Error> {
        let inner = match message_type(message) {
            Some(MessageType::Initial) => {
                let decoded = decode_initial(message).map_err(Error::Decode)?;
                match self.established_ephemeral.as_ref() {
                    Some(e)
                        if *e == decoded.ephemeral
                            && decoded.identity == encode_ec(&self.peer_identity_public) =>
                    {
                        decoded.message
                    }
                    _ => return Err(Error::NotARepeatedInitial),
                }
            }
            _ => message.to_vec(),
        };
        let plaintext = self.decrypt_ratchet(&inner, rng)?;
        // The peer has answered, so the initial message no longer needs
        // repeating. Only a successful decrypt counts: anything less is not
        // evidence that they established anything.
        self.pending_initial = None;
        Ok(plaintext)
    }

    fn decrypt_ratchet<R: RngCore + CryptoRng>(
        &mut self,
        message: &[u8],
        rng: &mut R,
    ) -> Result<Vec<u8>, Error> {
        // A failed agreement is terminal: nothing received after the message
        // that revealed it can advance the post-quantum ratchet, so refuse and
        // let the application re-establish.
        if self.braid.failed() {
            return Err(Error::AgreementFailed);
        }

        let decoded = decode_message(message).map_err(Error::Decode)?;

        // **Every state change here is provisional until the tag verifies.**
        //
        // Receiving mutates a great deal: it can delete a stored skipped key,
        // derive and store more of them, take a DH step, replace the root and
        // chain keys, and advance the receive counter. All of that is driven by
        // a header an attacker can write, and none of it is authenticated until
        // `aead::decrypt` checks the tag at the end.
        //
        // So it runs against a copy. The Double Ratchet specification is
        // explicit that an exception, authentication failure included, discards
        // the message *and* the state changes it would have made (section 3.5).
        // Done in place, a single flipped byte would advance the receive
        // counter and consume the message key of a genuine message still in
        // flight, which then could not be decrypted: an availability attack
        // available to anyone who can alter a captured frame.
        //
        // The copy costs one clone of the skipped-key store per received
        // message. `State` is `ZeroizeOnDrop`, so the copy that loses -- the
        // candidate on failure, the old state on success -- is wiped rather
        // than left on the heap.
        // Both halves are candidate-shaped, so nothing below commits until the
        // ciphertext has authenticated. `Braid::receive` and `Triple::receive`
        // each take `&self` and hand back a next state.
        let composite = decoded.header;

        // The agreement first, for the same reason as on the send side: the
        // ratchet needs the epoch and output it yields.
        let (ag_epoch, ag_out, braid_candidate) = self.braid.receive(&msg_of(&composite));
        let spqr_output = ag_out
            .as_ref()
            .map(|o| tacenta_spqr::Output::new(o.key_epoch, o.key));
        let _ = ag_epoch;

        // `peer` is the ratchet public key off an incoming message, so it is
        // attacker-chosen on every receive, not just at handshake time. A
        // low-order value here would hand the sender both agreements.
        let peer = dh::PublicKeyBytes::from_bytes(composite.dh);
        let nc = Error::Handshake(SessionError::NonContributoryAgreement);
        // Wiped on the way out: `dh_out_recv` seeds the new receiving chain and
        // `dh_out_send` the new sending chain, and both are `KDF_RK` inputs the
        // specifications require deleting once the next root key is derived
        // (CR-08, key-deletion.md). `dh_out_send` is computed on every receive
        // whether or not a step happens, so it is wrapped unconditionally.
        let dh_out_recv = Zeroizing::new(self.ratchet_private.agree(&peer).ok_or(nc)?);
        let candidate_key = dh::PrivateKey::from_bytes(random_secret(rng));
        let dh_out_send = Zeroizing::new(candidate_key.agree(&peer).ok_or(nc)?);

        let before = self.triple.sending_public();
        let header = triple_header_of(&composite);
        let new_dhs_pub = *candidate_key.public_key().as_bytes();

        // **A full skipped-key store makes room rather than refusing forever.**
        // Both ratchets refuse with `SkippedStoreFull` and only shrink their
        // stores on a *successful* receive, so once a store is full and one
        // live-chain message is missing, every later message needs a slot, is
        // refused, and never advances the clock that would free it: without
        // this, a lossy link would wedge the receive direction until the
        // session was re-established.
        //
        // The ordinary path costs what it always did: one `receive`, which
        // clones internally and hands back a candidate. Only a full store
        // pays for a second copy, `work`, which is evicted from and retried.
        // `work` reaches `self` only through `triple_candidate`, assigned
        // below and only after the tag verifies, so a forged header still
        // evicts nothing: the copy it drove is dropped with it.
        //
        // The first eviction aims at the shortfall the header implies rather
        // than climbing 1, 2, 4, ... up to it (CR-19). The classical ratchet
        // refuses when the keys it holds plus the keys this message skips on
        // the current chain -- its header number minus the current receive
        // count -- would exceed `MAX_SKIPPED_STORE`, so the room it needs is
        // that excess and nothing more, and both terms are known before the
        // first attempt. "Full" does not mean the store holds exactly the cap:
        // a store of 1500 keys refuses a message 600 ahead, and needs 100
        // evicted, not 600. Starting at the excess means a forged full-store
        // header no longer buys a run of eviction-and-retry rounds, each
        // cloning the 2000-entry store and deriving up to `MAX_SKIP` keys,
        // before it is refused.
        //
        // The post-quantum half is sized the same way, from the same two
        // figures read for the epoch its header names: the keys it holds
        // (`post_quantum_skipped_len`) and how far that epoch's receiving chain
        // has already got (`post_quantum_receive_count`). Its header number is
        // an absolute per-epoch index rather than a shortfall, which is why the
        // receive count is needed to turn one into the other: a message
        // numbered `n` skips `n - 1 - received` keys on that chain, and the
        // store refuses when the keys it holds plus that figure would exceed
        // `MAX_SKIPPED_STORE`, so the room it needs is that excess.
        //
        // The ramp stays as the fallback for a header naming an epoch the state
        // holds no receiving chain for, where the accessor reports nothing and
        // there is no figure to start from. `receive` folds a pending agreement
        // output in before it touches a chain, so the chain such a header wants
        // exists only once that has happened, and a shortfall computed from
        // what the state holds now would be about the wrong chain.
        //
        // Nothing a session sends produces that header. The agreement reports
        // the epoch both parties are known to hold, which is one behind the
        // sender's own, so the message carrying the output that opens epoch `e`
        // is itself stamped `e - 1`, and the accessor answers for a chain that
        // is already open. A header naming an epoch already *retired* does not
        // arrive here either: the sparse ratchet answers `NoChain`, which
        // `full_store` does not recognise, so this function returns before any
        // eviction is sized. The branch is therefore defensive, and
        // `store_eviction.rs` reaches it the only way anything can -- with a
        // forged header naming the epoch a fold is about to open -- to pin that
        // the ramp evicts from the working copy and commits none of it.
        //
        // Each half's figure carries one honest imprecision, in opposite
        // directions and both benign. The classical one counts the current
        // chain only: a message that also steps the ratchet first skips the
        // rest of the previous chain, whose length is not in the header, so on
        // a step it is an *under*-estimate and the geometric growth below
        // covers the rest. The post-quantum one reads the held count before the
        // fold, which may retire an epoch and drop its keys, so it can be an
        // *over*-estimate -- by at most what that retirement dropped, and never
        // by enough to empty the store: a store-full refusal means the message
        // skips at most `MAX_SKIP` keys, so the batch is at most
        // `held + MAX_SKIP - MAX_SKIPPED_STORE` and leaves at least
        // `MAX_SKIPPED_STORE - MAX_SKIP` keys standing whatever it evicts.
        // Stated against the two constants rather than as `held - MAX_SKIP`,
        // which is the same figure only while `MAX_SKIPPED_STORE` is exactly
        // twice `MAX_SKIP`; both are public and tunable, and the argument is
        // meant to survive one of them moving. At today's values that floor is
        // a thousand keys. Either way the first batch never exceeds what the
        // message displaces.
        //
        // The batch is reset when the *other* store reports full, because the
        // classical half runs first inside `receive` and a batch sized for its
        // need must not be spent on the post-quantum store, whose need is
        // unrelated.
        //
        // The figures are read from the copy being evicted from, not from
        // `self`: the two agree on the first attempt, and an eviction from one
        // store never touches the other, so they agree on every later one too,
        // but reading `work` makes that true by construction rather than by
        // argument.
        let shortfall = |half: FullStore, state: &tacenta_triple::State| -> usize {
            match half {
                FullStore::Classical => {
                    let held = state.classical_skipped_len();
                    let need =
                        (composite.n as usize).saturating_sub(state.receive_count() as usize);
                    held.saturating_add(need)
                        .saturating_sub(crate::ratchet::MAX_SKIPPED_STORE)
                        .max(1)
                }
                // `None` is the epoch the state holds no receiving chain for,
                // which is the fallback case above: nothing to compute from, so
                // the ramp starts at one.
                FullStore::PostQuantum => {
                    match state.post_quantum_receive_count(composite.pq_epoch) {
                        Some(received) => {
                            let held = state.post_quantum_skipped_len();
                            // The skip count the sparse ratchet computes, in its
                            // own arithmetic: it steps the chain to `n - 1`
                            // saturating, so a message numbered zero asks to skip
                            // nothing rather than wrapping. Widened saturating
                            // too, for the platforms where a `u64` does not fit a
                            // `usize`; the value is under `MAX_SKIP` on every path
                            // that reaches here.
                            let need = usize::try_from(
                                composite.pq_n.saturating_sub(1).saturating_sub(received),
                            )
                            .unwrap_or(usize::MAX);
                            held.saturating_add(need)
                                .saturating_sub(tacenta_spqr::MAX_SKIPPED_STORE)
                                .max(1)
                        }
                        None => 1,
                    }
                }
            }
        };
        let receive = |state: &tacenta_triple::State| {
            state.receive(
                &header,
                &dh_out_recv,
                &dh_out_send,
                new_dhs_pub,
                spqr_output.as_ref(),
            )
        };
        let (triple_candidate, mk) = match receive(&self.triple) {
            Ok(v) => v,
            Err(first) => {
                let Some(mut half) = full_store(&first) else {
                    return Err(Error::Triple(first));
                };
                let mut work = self.triple.clone();
                let mut batch: usize = shortfall(half, &work);
                let mut pending = first;
                loop {
                    let evicted = match half {
                        FullStore::Classical => work.evict_oldest_classical(batch),
                        FullStore::PostQuantum => work.evict_oldest_post_quantum(batch),
                    };
                    if evicted == 0 {
                        return Err(Error::Triple(pending));
                    }
                    // Bounded: the stores hold at most `MAX_SKIPPED_STORE`
                    // keys each, so this doubles a dozen times at most before
                    // an eviction returns zero. Saturating so it cannot
                    // overflow when the initial batch is already large.
                    batch = batch.saturating_mul(2);
                    match receive(&work) {
                        Ok(v) => break v,
                        Err(e) => {
                            let Some(next) = full_store(&e) else {
                                return Err(Error::Triple(e));
                            };
                            if next != half {
                                half = next;
                                batch = shortfall(next, &work);
                            }
                            pending = e;
                        }
                    }
                }
            }
        };

        // Wiped on the way out: the message key and the AEAD material derived
        // from it were bare arrays on the stack.
        let mk = Zeroizing::new(mk);
        let keys = Zeroizing::new(ratchet::message_keys(&mk, ratchet::LabelSet::Tacenta));
        let (enc, mac, iv) = &*keys;
        let ad = concat_ad(&self.identity_ad, &composite);
        let plaintext =
            aead::decrypt(enc, mac, iv, &decoded.ciphertext, &ad).map_err(|_| Error::Aead)?;

        // Authenticated. Commit, and not before: the assignments below are the
        // only place this function writes to `self`, and they are all of it.
        if triple_candidate.sending_public() != before {
            self.ratchet_private = candidate_key;
        }
        self.triple = triple_candidate;
        self.braid = braid_candidate;
        Ok(plaintext)
    }
}

/// This module's own persistence-format version (`Session::export`/
/// `import`), separate from any on-the-wire message version: this is what a
/// storage layer writes to disk and reads back after a restart, not anything
/// a peer ever receives.
const SESSION_VERSION: u8 = 0x01;

/// A `Session::export`/`import` failure. As in every format this composes,
/// the threat model is corruption and version skew, not a hostile peer.
/// Named apart from this module's own `DecodeError` (a wire-message decode
/// failure) so the two are never confused for one another.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum SessionDecodeError {
    UnknownVersion,
    TooShort,
    Malformed,
    /// The bytes decoded, and re-encoding the result did not reproduce them.
    ///
    /// Something in the nested decode accepted a spelling `export` would never
    /// emit -- padding behind an absent-field tag, most likely. The state may be
    /// perfectly ordinary; what is not ordinary is the byte string that carried
    /// it, and a stored blob that is not the encoding of what it decodes to
    /// cannot be authenticated by anything computed over exact bytes.
    NonCanonical,
    /// The bytes decoded, canonically, to a session no constructor builds
    /// and no operation preserves: [`Session::invariant`] is false of it.
    ///
    /// Distinct from `NonCanonical`, which is about the byte string, and
    /// from `Malformed`, which is about one field. Every clause of the
    /// invariant is a relation *between* fields -- the ratchet private key
    /// and the public key the ratchet advertises, the sparse ratchet's epoch
    /// and the Braid's, the associated data and the role -- which a
    /// field-by-field decode accepts one field at a time and which,
    /// accepted, does not fail at import but on some later message, and in
    /// the first two cases for good. Refused here so that a session which
    /// imports is one that can go on.
    Inconsistent,
}

fn push_len_prefixed(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
    out.extend_from_slice(bytes);
}

fn take_len_prefixed(bytes: &[u8], pos: usize) -> Option<(&[u8], usize)> {
    // `checked_add` on both sums. On a 32-bit target a length near
    // `u32::MAX` would make `start + len` wrap, pass the bounds check, and
    // panic on the slice: the same class `serialization::take_at` guards
    // against for the wire decoders.
    let start = pos.checked_add(4)?;
    if bytes.len() < start {
        return None;
    }
    let mut len_bytes = [0u8; 4];
    len_bytes.copy_from_slice(&bytes[pos..start]);
    let len = u32::from_be_bytes(len_bytes) as usize;
    let end = start.checked_add(len)?;
    if bytes.len() < end {
        return None;
    }
    Some((&bytes[start..end], end))
}

impl PendingInitial {
    fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(self.ephemeral_public.as_bytes());
        push_len_prefixed(&mut out, &self.kem_ciphertext);
        out.extend_from_slice(&self.signed_prekey_id.to_be_bytes());
        out.extend_from_slice(&self.one_time_prekey_id.to_be_bytes());
        out.extend_from_slice(&self.kem_prekey_id.to_be_bytes());
        out
    }

    fn from_bytes(bytes: &[u8]) -> Option<PendingInitial> {
        if bytes.len() < 32 {
            return None;
        }
        let mut ephemeral_public = [0u8; 32];
        ephemeral_public.copy_from_slice(&bytes[0..32]);
        let (kem_ciphertext, pos) = take_len_prefixed(bytes, 32)?;
        let kem_ciphertext = kem_ciphertext.to_vec();
        if bytes.len() != pos + 12 {
            return None;
        }
        let mut a = [0u8; 4];
        a.copy_from_slice(&bytes[pos..pos + 4]);
        let mut b = [0u8; 4];
        b.copy_from_slice(&bytes[pos + 4..pos + 8]);
        let mut c = [0u8; 4];
        c.copy_from_slice(&bytes[pos + 8..pos + 12]);
        Some(PendingInitial {
            ephemeral_public: dh::PublicKeyBytes::from_bytes(ephemeral_public),
            kem_ciphertext,
            signed_prekey_id: u32::from_be_bytes(a),
            one_time_prekey_id: u32::from_be_bytes(b),
            kem_prekey_id: u32::from_be_bytes(c),
        })
    }
}

impl Session {
    /// Encode this session for persistence: the version byte, then each
    /// field, length-prefixed where its width is not fixed. Not a message on
    /// the wire -- see `crate::serialization` for that -- this is what a
    /// storage layer writes to disk and reads back with `import` after a
    /// restart. At-rest protection of the persisted bytes is that caller's
    /// job, the same as for every format this composes (`key-deletion.md`'s
    /// in-memory-only erasure claim does not extend to storage media by
    /// itself).
    ///
    /// **When to persist, and in what order.** The ordering rules a storage
    /// layer must keep, stated here because nothing in the types enforces
    /// them:
    ///
    /// 1. **Persist before transmitting.** After `encrypt` returns, write the
    ///    session before the ciphertext leaves this device. A crash between
    ///    the two restarts from a state that has not spent that message key,
    ///    so the next `encrypt` derives the *same* key and IV for a different
    ///    plaintext under AES-CBC, which leaks plaintext-prefix equality and
    ///    spends both ratchets' keys twice.
    /// 2. **Persist before acknowledging.** After `decrypt` returns, write the
    ///    session before treating the message as received. A crash in
    ///    between replays the old state; the message decrypts again on
    ///    restart, which is harmless, but the skipped keys it consumed are
    ///    live again.
    /// 3. **Session before store, on establishment.** `establish_responder`
    ///    returns a new session *and* mutates the prekey store (deleting the
    ///    one-time prekeys the message used, recording a last-resort
    ///    fingerprint). Write the session first, then the store, in one
    ///    transaction where the medium offers one. Store first and a crash
    ///    between the two deletes the prekey the session was never persisted
    ///    from: the peer's first message is undecryptable for good, and since
    ///    an initiator repeats it until answered, so is every message after.
    ///    Session first and a crash between the two leaves the one-time
    ///    prekey in the store after its session exists, so a replay of the
    ///    captured initial message opens a duplicate session from the same
    ///    secret; the last-resort fingerprint record exists to refuse exactly
    ///    that on the multi-use path, and it too must be persisted for it to
    ///    hold across a restart.
    pub fn export(&self) -> Zeroizing<Vec<u8>> {
        // Each part encoded once, then the buffer sized exactly, so it never
        // grows and leaves an outgrown allocation of secret bytes un-wiped
        // (`PrekeyStore::to_bytes` says more).
        let triple = self.triple.to_bytes();
        let braid = self.braid.to_bytes();
        let ratchet_private = self.ratchet_private.to_bytes();
        let pending = self.pending_initial.as_ref().map(|p| p.to_bytes());
        let capacity = 1
            + (4 + triple.len())
            + (4 + braid.len())
            + ratchet_private.len()
            + (4 + self.identity_ad.len())
            + 32
            + 32
            + 1
            + pending.as_ref().map_or(0, |p| 4 + p.len())
            + 1
            + self
                .established_ephemeral
                .as_ref()
                .map_or(0, |e| 4 + e.len());
        let mut out = Vec::with_capacity(capacity);
        out.push(SESSION_VERSION);
        push_len_prefixed(&mut out, &triple);
        push_len_prefixed(&mut out, &braid);
        out.extend_from_slice(&*ratchet_private);
        push_len_prefixed(&mut out, &self.identity_ad);
        out.extend_from_slice(self.our_identity_public.as_bytes());
        out.extend_from_slice(self.peer_identity_public.as_bytes());
        match &pending {
            None => out.push(0x00),
            Some(p) => {
                out.push(0x01);
                push_len_prefixed(&mut out, p);
            }
        }
        match &self.established_ephemeral {
            None => out.push(0x00),
            Some(e) => {
                out.push(0x01);
                push_len_prefixed(&mut out, e);
            }
        }
        debug_assert_eq!(
            out.len(),
            capacity,
            "the size arithmetic above drifted from the encoding"
        );
        Zeroizing::new(out)
    }

    /// Decode a session persisted by `export`.
    /// Restore a session from [`Session::export`].
    ///
    /// **This is the trust boundary for persisted state, and it is enforced
    /// here rather than in the decoders.** Every persisted session in the
    /// product reaches live state through this function, which its session
    /// restore path calls once per session. The nested `from_bytes` implementations
    /// live in the verified crates, where a change re-runs Charon and Aeneas
    /// and reopens the T1 and T3 theorems; this function does not, so the check
    /// costs nothing in proof work and sits exactly where untrusted bytes
    /// arrive.
    ///
    /// The check is a **re-encode and compare**. If the bytes decoded to a
    /// state that does not encode back to the same bytes, they were not
    /// produced by `export`, and they are refused. That catches
    /// non-canonical acceptance anywhere in the nested decode without this
    /// function needing to know where -- which is the property that makes it
    /// worth doing here rather than field by field.
    ///
    /// **What the re-encode does not catch**, and what the second check is
    /// for: a byte string that is canonical and describes a session no
    /// constructor builds. A ratchet private key beside an advertised public
    /// key that is not its own re-encodes to itself and passes; so does an
    /// epoch pair the sparse ratchet cannot follow. Those are relations
    /// *between* fields, and [`Session::invariant`] states them: a session
    /// for which it is false is refused as `Inconsistent`, after the
    /// re-encode, so that the error names the more specific of the two
    /// things wrong with the bytes. What remains uncaught is a canonical,
    /// consistent state that is merely extreme -- a saturated counter --
    /// which is a property whose check belongs at the use site, not here.
    pub fn import(bytes: &[u8]) -> Result<Session, SessionDecodeError> {
        let session = Session::import_unchecked(bytes)?;
        if session.export().as_slice() != bytes {
            return Err(SessionDecodeError::NonCanonical);
        }
        if !session.invariant() {
            return Err(SessionDecodeError::Inconsistent);
        }
        Ok(session)
    }

    /// Whether this session is one the constructors build and the operations
    /// preserve.
    ///
    /// The relations between fields that a field-by-field decode cannot see.
    /// [`import`](Session::import) refuses a session for which this is false
    /// (`SessionDecodeError::Inconsistent`), and the tests and the fuzz
    /// targets assert it after every establishment, message and round trip,
    /// so that it is checked as an inductive invariant -- established by the
    /// constructors, preserved by every operation, re-established at the
    /// persistence boundary -- rather than trusted at one point. Each clause
    /// says what accepting its violation would cost, because none of them
    /// fails at import: each fails on some later message, and the first two
    /// for good.
    ///
    /// What it does not check is anything a hostile writer of the storage
    /// medium could still forge: key material is bytes, and no relation
    /// between fields says whether a root key is the one the peer holds.
    /// That is at-rest protection, which session-persistence.md places with
    /// the caller.
    pub fn invariant(&self) -> bool {
        // (a) The ratchet private key is the private half of the public key
        // the classical ratchet advertises in its headers. The peer agrees
        // against the advertised key and this side against the private one,
        // so a mismatch survives until the peer's next Diffie-Hellman step
        // and then breaks every message after it, for good: the two sides
        // derive different root keys and nothing ever reconciles them.
        if *self.ratchet_private.public_key().as_bytes() != self.triple.sending_public() {
            return false;
        }

        // (b) The sparse ratchet's epoch and the Braid's stand in the
        // relation every persistence point has. The Braid negotiates epoch
        // `e`; the sparse ratchet holds the last epoch whose secret was
        // folded in. The fold happens at one of two transitions, and both
        // sides pass through both over the session's life because the roles
        // swap each epoch: the header-receiving side folds when it samples
        // `ct1` (Ct1Sampled, tag 7, and the three states after it, tags 8
        // to 10), and the header-sending side folds when it decapsulates
        // `ct2` (transition 5), which advances the Braid to `e + 1` in the
        // same step. So the sparse ratchet is at `e` in tags 7 through 10
        // and at `e - 1` in tags 0 through 6, and `Session::encrypt` and
        // `decrypt_ratchet` commit both halves together, so there is no
        // point between. Confirmed over two hundred epochs of honest traffic
        // when this clause was written; tests/import_invariants.rs holds
        // about fifty of them, from both roles, at every message and round
        // trip. A failed Braid reports no epoch and is exempt: a failure is
        // terminal and persisted as such. Outside this relation the sparse ratchet refuses the next
        // agreement output as `EpochOutOfOrder`, on every message, and the
        // session never recovers -- the external review's 346 failures in
        // 400 round trips.
        if !self.braid.failed() {
            let braid_epoch = self.braid.epoch();
            let folded = self.triple.epoch();
            let related = match self.braid.state_tag() {
                7..=10 => folded == braid_epoch,
                _ => folded.checked_add(1) == Some(braid_epoch),
            };
            if !related {
                return false;
            }
        }

        // (c) The associated data binds the two identities in the orientation
        // the role fixes: initiator first. Which side this session is on is
        // read from `established_ephemeral`, which every responder carries
        // for its whole life (`establish_responder` sets it and nothing
        // clears it) and no initiator ever has; `pending_initial` would not
        // do, since an initiator drops it once the peer answers. The Braid
        // carries the same fact and is compared against it below rather than
        // read as the source, because a role read from the Braid could not
        // then be checked against the Braid. Wrong orientation is an AEAD
        // failure on every message in both directions, since the peer
        // computes its own from the same rule.
        let (initiator, responder) = if self.is_responder() {
            (&self.peer_identity_public, &self.our_identity_public)
        } else {
            (&self.our_identity_public, &self.peer_identity_public)
        };
        if self.identity_ad != identity_ad(initiator, responder) {
            return false;
        }

        // (d) The halves agree on the role. The Braid reports its own
        // (`is_initiator`: the initiator sends the first epoch's header and
        // the sides swap each epoch, so the party that started as initiator
        // is on the header-sending side in every odd epoch; `None` once
        // failed, which has no role left). A Braid on the wrong side of an
        // epoch waits for the messages the peer is waiting for, and the
        // agreement stalls without failing. The sparse ratchet's `Direction`
        // is the role too, fixed at `init_alice`/`init_bob` and never
        // changed -- `A2b` is the initiator's, since `init_sender` pairs the
        // classical sender with it -- and a session on the wrong one sends
        // on the chain the peer receives on and reads the peer's sends
        // against the wrong chain key, so nothing decrypts. The classical
        // ratchet shows its role only until its first Diffie-Hellman step
        // (both sides then hold both chains), and the Triple Ratchet's own
        // invariant checks it against the sparse ratchet's while it can, so
        // it is reached through clause (g) rather than repeated here.
        if let Some(braid_initiator) = self.braid.is_initiator() {
            if braid_initiator == self.is_responder() {
                return false;
            }
        }
        if (self.triple.direction() == Direction::A2b) == self.is_responder() {
            return false;
        }

        // (e) An initiator that is still to be answered is not also a
        // responder. `pending_initial` is the initiator's unanswered initial
        // message and `established_ephemeral` the responder's record of the
        // one it answered; a session holding both would prepend a prekey
        // message to every send while accepting repeats of a different one.
        if self.pending_initial.is_some() && self.established_ephemeral.is_some() {
            return false;
        }

        // (f) The pending initial message's KEM ciphertext has the length the
        // KEM produces, and the established ephemeral is an `EncodeEC` value:
        // 33 bytes, the curve byte first. Neither is checked where it is
        // used. `encode_initial` length-prefixes whatever it is given, so a
        // ciphertext of the wrong length would go out on every repeat of the
        // initial message and be refused by the peer's decapsulation each
        // time; and a repeated initial message is matched against
        // `established_ephemeral` byte for byte, so a value no initiator can
        // send makes every repeat look like a different establishment.
        if let Some(p) = &self.pending_initial {
            if p.kem_ciphertext.len() != kem::ciphertext_len() {
                return false;
            }
        }
        if let Some(e) = &self.established_ephemeral {
            if decode_ec(e).is_none() {
                return false;
            }
        }

        // (h) Every curve public key the session stores is its canonical
        // encoding, as (f) holds the established ephemeral's to
        // (session-persistence.md, Stored curve public keys). Each is used as
        // its bytes: (c) compares the associated data with `EncodeEC` of the
        // two identities, a repeat's `identity` is compared with the peer's,
        // `peer_identity()` reports it, and every repeat of the initial
        // message carries our identity and the pending ephemeral, which the
        // peer's decoder refuses in any other spelling. Every constructor
        // stores keys X25519 computed, keys a decoder accepted, or a bundle's
        // keys, which `establish_initiator_for` checks. The ratchet's own
        // keys are its crate's invariant's, reached through (g). Lettered
        // after (g), which was there first, and checked before it because
        // (g) is the function's last expression.
        if !is_canonical_key(&self.our_identity_public)
            || !is_canonical_key(&self.peer_identity_public)
        {
            return false;
        }
        if let Some(p) = &self.pending_initial {
            if !is_canonical_key(&p.ephemeral_public) {
                return false;
            }
        }

        // (g) Each half is one its own constructors build. The Triple
        // Ratchet's predicate covers both ratchets and their agreement on the
        // role; the Braid's covers its twelve states and the coders inside
        // them. Both decoders refuse on their own predicate, so at import
        // this is a second reading, and after a message it is the only one.
        self.triple.invariant() && self.braid.invariant()
    }

    /// Which side of the handshake this session is on, read from the one
    /// field that says so for a session's whole life. Clause (c) of
    /// [`invariant`](Session::invariant) says why this field and not
    /// `pending_initial`.
    fn is_responder(&self) -> bool {
        self.established_ephemeral.is_some()
    }

    fn import_unchecked(bytes: &[u8]) -> Result<Session, SessionDecodeError> {
        if bytes.is_empty() {
            return Err(SessionDecodeError::TooShort);
        }
        if bytes[0] != SESSION_VERSION {
            return Err(SessionDecodeError::UnknownVersion);
        }
        let Some((triple_bytes, pos)) = take_len_prefixed(bytes, 1) else {
            return Err(SessionDecodeError::TooShort);
        };
        let Ok(triple) = tacenta_triple::State::from_bytes(triple_bytes) else {
            return Err(SessionDecodeError::Malformed);
        };
        let Some((braid_bytes, pos)) = take_len_prefixed(bytes, pos) else {
            return Err(SessionDecodeError::TooShort);
        };
        let Ok(braid) = tacenta_braid::Braid::from_bytes(braid_bytes) else {
            return Err(SessionDecodeError::Malformed);
        };
        if bytes.len() < pos + 32 {
            return Err(SessionDecodeError::TooShort);
        }
        let mut ratchet_private_bytes = [0u8; 32];
        ratchet_private_bytes.copy_from_slice(&bytes[pos..pos + 32]);
        let ratchet_private = dh::PrivateKey::from_bytes(ratchet_private_bytes);
        let pos = pos + 32;

        let Some((identity_ad, pos)) = take_len_prefixed(bytes, pos) else {
            return Err(SessionDecodeError::TooShort);
        };
        let identity_ad = identity_ad.to_vec();

        if bytes.len() < pos + 64 {
            return Err(SessionDecodeError::TooShort);
        }
        let mut our_pub = [0u8; 32];
        our_pub.copy_from_slice(&bytes[pos..pos + 32]);
        let mut peer_pub = [0u8; 32];
        peer_pub.copy_from_slice(&bytes[pos + 32..pos + 64]);
        let pos = pos + 64;

        if bytes.len() < pos + 1 {
            return Err(SessionDecodeError::TooShort);
        }
        let (pending_initial, pos) = match bytes[pos] {
            0x00 => (None, pos + 1),
            0x01 => {
                let Some((p_bytes, next)) = take_len_prefixed(bytes, pos + 1) else {
                    return Err(SessionDecodeError::TooShort);
                };
                let Some(p) = PendingInitial::from_bytes(p_bytes) else {
                    return Err(SessionDecodeError::Malformed);
                };
                (Some(p), next)
            }
            _ => return Err(SessionDecodeError::Malformed),
        };

        if bytes.len() < pos + 1 {
            return Err(SessionDecodeError::TooShort);
        }
        let (established_ephemeral, pos) = match bytes[pos] {
            0x00 => (None, pos + 1),
            0x01 => {
                let Some((e_bytes, next)) = take_len_prefixed(bytes, pos + 1) else {
                    return Err(SessionDecodeError::TooShort);
                };
                (Some(e_bytes.to_vec()), next)
            }
            _ => return Err(SessionDecodeError::Malformed),
        };

        if pos != bytes.len() {
            return Err(SessionDecodeError::Malformed);
        }

        Ok(Session {
            triple,
            braid,
            ratchet_private,
            identity_ad,
            our_identity_public: dh::PublicKeyBytes::from_bytes(our_pub),
            peer_identity_public: dh::PublicKeyBytes::from_bytes(peer_pub),
            pending_initial,
            established_ephemeral,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A bundle fetched just before the signed prekey rotated still
    /// establishes; one fetched before the rotation before that does not.
    /// Multi-use bundles, so that no one-time prekey is consumed and the only
    /// identifier in question is the signed one.
    #[test]
    fn a_rotated_signed_prekey_is_honoured_for_one_rotation() {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(2);
        let alice = Identity::generate(&mut rng);
        let bob = Identity::generate(&mut rng);
        let mut store = bob.create_prekeys(2, &mut rng);

        let before = store.publish_multi_use();
        store.rotate_signed_prekey(&bob, &mut rng);
        let after = store.publish_multi_use();
        assert_ne!(before.signed_prekey_id, after.signed_prekey_id);

        let mut s = establish_initiator(&alice, &before, &mut rng).unwrap();
        let m = s.encrypt(b"fetched before the rotation", &mut rng).unwrap();
        let (_, pt) = establish_responder(&bob, &mut store, &m, &mut rng).unwrap();
        assert_eq!(pt, b"fetched before the rotation");

        store.rotate_signed_prekey(&bob, &mut rng);
        let mut s2 = establish_initiator(&alice, &before, &mut rng).unwrap();
        let m2 = s2.encrypt(b"two rotations ago", &mut rng).unwrap();
        assert!(matches!(
            establish_responder(&bob, &mut store, &m2, &mut rng),
            Err(Error::UnknownPrekeyId)
        ));

        // `after` is now the retired one, and still good.
        let mut s3 = establish_initiator(&alice, &after, &mut rng).unwrap();
        let m3 = s3.encrypt(b"one rotation ago", &mut rng).unwrap();
        let (_, pt3) = establish_responder(&bob, &mut store, &m3, &mut rng).unwrap();
        assert_eq!(pt3, b"one rotation ago");
    }

    /// The same for the last-resort KEM prekey, whose retired copy is still a
    /// last-resort key: a replay against it is refused as one.
    #[test]
    fn a_rotated_last_resort_kem_prekey_is_honoured_for_one_rotation() {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(3);
        let alice = Identity::generate(&mut rng);
        let bob = Identity::generate(&mut rng);
        let mut store = bob.create_prekeys(2, &mut rng);

        let before = store.publish_multi_use();
        store.rotate_kem(&bob, &mut rng);
        assert_ne!(before.kem_prekey_id, store.kem_id);

        let mut s = establish_initiator(&alice, &before, &mut rng).unwrap();
        let m = s.encrypt(b"retired key", &mut rng).unwrap();
        let (_, pt) = establish_responder(&bob, &mut store, &m, &mut rng).unwrap();
        assert_eq!(pt, b"retired key");
        assert!(matches!(
            establish_responder(&bob, &mut store, &m, &mut rng),
            Err(Error::ReplayedLastResort)
        ));

        // The entry is tagged with the key it was made against, and survives
        // the first rotation because that key still decrypts.
        assert_eq!(
            store
                .last_resort_seen
                .iter()
                .map(|(id, _)| *id)
                .collect::<Vec<_>>(),
            vec![before.kem_prekey_id]
        );

        store.rotate_kem(&bob, &mut rng);
        let mut s2 = establish_initiator(&alice, &before, &mut rng).unwrap();
        let m2 = s2.encrypt(b"gone", &mut rng).unwrap();
        assert!(matches!(
            establish_responder(&bob, &mut store, &m2, &mut rng),
            Err(Error::UnknownPrekeyId)
        ));
        // The second rotation wiped that key, and its entry went with it: a
        // message naming a wiped key fails before the record is consulted, so
        // the entry could refuse nothing.
        assert!(store.last_resort_seen.is_empty());
    }

    /// The retired prekeys survive persistence, and a v2 store -- the format
    /// before rotation -- still reads back, with nothing retired.
    #[test]
    fn to_bytes_from_bytes_round_trips_the_retired_prekeys() {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(4);
        let bob = Identity::generate(&mut rng);
        let mut store = bob.create_prekeys(2, &mut rng);
        store.rotate_signed_prekey(&bob, &mut rng);
        store.rotate_kem(&bob, &mut rng);

        let bytes = store.to_bytes();
        let restored = PrekeyStore::from_bytes(&bytes).unwrap();
        assert_eq!(
            restored
                .previous_signed_prekey
                .map(|(s, id, sig)| (s, id, sig.to_vec())),
            store
                .previous_signed_prekey
                .map(|(s, id, sig)| (s, id, sig.to_vec()))
        );
        assert_eq!(
            restored
                .previous_kem
                .as_ref()
                .map(|(p, id, _)| (p.to_bytes(), *id)),
            store
                .previous_kem
                .as_ref()
                .map(|(p, id, _)| (p.to_bytes(), *id))
        );
        assert_eq!(restored.to_bytes(), bytes);

        // Truncating the retired-prekey tail and relabelling as v2 is exactly
        // a v2 store: with no record entries there are no tags to strip.
        let fresh = bob.create_prekeys(2, &mut rng);
        let mut v2 = fresh.to_bytes().to_vec();
        assert_eq!(&v2[v2.len() - 2..], &[0x00, 0x00]);
        v2.truncate(v2.len() - 2);
        v2[0] = PREKEY_STORE_VERSION_V2;
        let from_v2 = PrekeyStore::from_bytes(&v2).unwrap();
        assert!(from_v2.previous_signed_prekey.is_none());
        assert!(from_v2.previous_kem.is_none());
        assert_eq!(from_v2.signed_prekey_id, fresh.signed_prekey_id);
    }

    /// A terminal post-quantum agreement is refused, not carried on with.
    ///
    /// The Braid's own contract is that `Failed` is terminal; a session that
    /// did not check would send an epoch-0 header on every later `encrypt`.
    /// The terminal state is reached here by decoding a Braid that is already
    /// `Failed` -- its encoding is the state version byte and the tag, nothing
    /// else -- because the honest-peer route to it (a crash between sending
    /// and persisting, on exactly a turn where the Braid samples a key pair)
    /// depends on timing a test cannot pin.
    #[test]
    fn a_failed_agreement_refuses_further_use() {
        use rand::SeedableRng;
        let mut r = rand::rngs::StdRng::seed_from_u64(11);
        let alice_id = Identity::generate(&mut r);
        let bob_id = Identity::generate(&mut r);
        let mut bob_prekeys = bob_id.create_prekeys(2, &mut r);
        let bundle = bob_prekeys.publish();
        let mut alice = establish_initiator(&alice_id, &bundle, &mut r).unwrap();
        let initial = alice.encrypt(b"hello", &mut r).unwrap();
        let (mut bob, _first) =
            establish_responder(&bob_id, &mut bob_prekeys, &initial, &mut r).unwrap();
        assert!(!bob.agreement_failed());

        // Force the terminal state. `State::Failed` carries no fields, so a
        // failed Braid encodes as the version byte followed by its tag (11).
        let version = bob.braid.to_bytes()[0];
        bob.braid = tacenta_braid::Braid::from_bytes(&[version, 11])
            .expect("a Failed braid decodes from the version byte and its tag");
        assert!(bob.agreement_failed());

        // Loud in both directions, not a silent epoch-0 session.
        assert!(matches!(
            bob.encrypt(b"x", &mut r),
            Err(Error::AgreementFailed)
        ));
        let from_alice = alice.encrypt(b"y", &mut r).unwrap();
        assert!(matches!(
            bob.decrypt(&from_alice, &mut r),
            Err(Error::AgreementFailed)
        ));
    }

    /// The identity and the prekey store erase themselves when dropped.
    ///
    /// Static, for the reason `tacenta-ratchet`'s own version of this test
    /// gives: freed memory is not something a test can inspect soundly, and
    /// what this pins is that the property cannot be dropped without the build
    /// failing. Both hold it by a route a derive would not give them --
    /// `PrekeyStore` by a hand-written destructor, because a whole-struct derive
    /// will not compile over its un-`Zeroize` fields (the public key and the
    /// self-erasing `kem::KeyPair`s) -- so there is nothing in the type
    /// declarations for a reader to notice.
    #[test]
    fn the_identity_and_the_prekey_store_erase_when_dropped() {
        fn assert_erases<T: zeroize::ZeroizeOnDrop>() {}
        assert_erases::<Identity>();
        assert_erases::<PrekeyStore>();
    }

    /// Every identifier a store hands out is distinct.
    ///
    /// The lookups find the first match, so a duplicate would let a one-time
    /// prekey be used twice. Nothing about a `Vec` enforces this, so it is
    /// checked.
    #[test]
    fn a_stores_identifiers_are_unique() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let store = id.create_prekeys(8, &mut rng);

        let mut ids: Vec<u32> = vec![store.signed_prekey_id, store.kem_id];
        ids.extend(store.one_time.iter().map(|(k, _)| *k));
        ids.extend(store.kem_one_time.iter().map(|(k, _, _)| *k));

        let mut sorted = ids.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), ids.len(), "a store handed out a repeated id");
        assert!(
            !ids.contains(&crate::serialization::ABSENT_ID),
            "an id collided with the absent-id sentinel"
        );
        assert!(
            ids.iter().all(|i| *i < store.next_id),
            "next_id must be past everything handed out"
        );
    }

    /// `create_prekeys` numbers a store as key-deletion.md gives, and stops at
    /// the end of the identifier space the way `replenish` does: `u32::MAX` is
    /// never issued, and no count wraps the counter.
    ///
    /// A store that reaches the end would hold four billion keys, so the
    /// boundary is tested through the numbering, and through a store whose
    /// counter is set to the end.
    #[test]
    fn create_prekeys_stops_at_the_end_of_the_identifier_space() {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::seed_from_u64(12);
        let id = Identity::generate(&mut rng);

        // A small store takes exactly the numbering, which is the
        // specification's for n = 2.
        let two = PrekeyNumbering::for_count(2);
        assert_eq!(
            two,
            PrekeyNumbering {
                signed_prekey: 1,
                one_time: 2..4,
                kem: 4,
                kem_one_time: 5..7,
                next_id: 7,
            }
        );
        let store = id.create_prekeys(2, &mut rng);
        assert_eq!(store.signed_prekey_id, two.signed_prekey);
        assert!(store.one_time.iter().map(|(k, _)| *k).eq(two.one_time));
        assert_eq!(store.kem_id, two.kem);
        assert!(
            store
                .kem_one_time
                .iter()
                .map(|(k, _, _)| *k)
                .eq(two.kem_one_time)
        );
        assert_eq!(store.next_id, two.next_id);

        // The largest count that fits issues identifiers up to u32::MAX - 1,
        // contiguous and in order, and leaves next_id at u32::MAX.
        assert_eq!(MAX_CREATED_ONE_TIME, (1u32 << 31) - 2);
        let top = PrekeyNumbering::for_count(MAX_CREATED_ONE_TIME as usize);
        assert_eq!(top.signed_prekey, 1);
        assert_eq!(top.one_time.start, 2);
        assert_eq!(top.one_time.len(), MAX_CREATED_ONE_TIME as usize);
        assert_eq!(top.one_time.end, top.kem);
        assert_eq!(top.kem_one_time.start, top.kem + 1);
        assert_eq!(top.kem_one_time.len(), MAX_CREATED_ONE_TIME as usize);
        assert_eq!(top.kem_one_time.clone().next_back(), Some(u32::MAX - 1));
        assert_eq!(top.kem_one_time.end, top.next_id);
        assert_eq!(top.next_id, u32::MAX);

        // One more does not fit, so the cap is exactly the bound, and every
        // count past it is numbered as the cap is.
        assert_eq!(PrekeyNumbering::checked(MAX_CREATED_ONE_TIME + 1), None);
        assert_eq!(
            PrekeyNumbering::for_count(MAX_CREATED_ONE_TIME as usize + 1),
            top
        );
        assert_eq!(PrekeyNumbering::for_count(usize::MAX), top);

        // A store at that end is one the invariant and the reader accept, and
        // nothing adds to it.
        let mut store = id.create_prekeys(1, &mut rng);
        store.kem_one_time[0].0 = u32::MAX - 1;
        store.next_id = u32::MAX;
        assert!(store.invariant());
        let restored = PrekeyStore::from_bytes(&store.to_bytes())
            .expect("a store whose next_id is u32::MAX reads back");
        assert_eq!(restored.next_id, u32::MAX);

        let before = store.to_bytes();
        store.replenish(&id, 1, &mut rng);
        store.rotate_signed_prekey(&id, &mut rng);
        store.rotate_kem(&id, &mut rng);
        assert_eq!(
            &store.to_bytes()[..],
            &before[..],
            "a key was issued past the end of the identifier space"
        );
        assert_eq!(store.next_id, u32::MAX);
    }

    /// Two stores built from one identity number themselves identically.
    ///
    /// This is the hazard `next_id` exists for, pinned so it is a documented
    /// property rather than a surprise. Replenishing by calling
    /// `create_prekeys` again and combining the results would produce a store
    /// with duplicate identifiers, and duplicates are how a one-time prekey
    /// gets used twice. Anything that adds keys must continue from `next_id`.
    #[test]
    fn two_stores_from_one_identity_collide_and_must_not_be_merged() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let first = id.create_prekeys(4, &mut rng);
        let second = id.create_prekeys(4, &mut rng);

        let ids = |s: &PrekeyStore| -> Vec<u32> {
            let mut v = vec![s.signed_prekey_id, s.kem_id];
            v.extend(s.one_time.iter().map(|(k, _)| *k));
            v.extend(s.kem_one_time.iter().map(|(k, _, _)| *k));
            v.sort_unstable();
            v
        };
        assert_eq!(
            ids(&first),
            ids(&second),
            "the hazard has changed shape; re-read PrekeyStore::next_id"
        );

        // And the keys behind those identical identifiers are different, which
        // is what makes a merge unsafe rather than merely redundant.
        assert_ne!(first.signed_prekey_secret, second.signed_prekey_secret);
    }

    /// A freshly created store round-trips field for field, and its
    /// `publish()` output is unchanged.
    #[test]
    fn to_bytes_from_bytes_round_trips_a_fresh_store() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let store = id.create_prekeys(4, &mut rng);

        let bytes = store.to_bytes();
        let restored = PrekeyStore::from_bytes(&bytes).unwrap();

        assert_eq!(
            restored.identity_public.as_bytes(),
            store.identity_public.as_bytes()
        );
        assert_eq!(restored.signed_prekey_secret, store.signed_prekey_secret);
        assert_eq!(restored.signed_prekey_id, store.signed_prekey_id);
        assert_eq!(restored.signed_prekey_sig, store.signed_prekey_sig);
        assert_eq!(restored.one_time, store.one_time);
        assert_eq!(restored.kem.public_key(), store.kem.public_key());
        assert_eq!(restored.kem_id, store.kem_id);
        assert_eq!(restored.kem_sig, store.kem_sig);
        assert_eq!(restored.kem_one_time.len(), store.kem_one_time.len());
        for (a, b) in restored.kem_one_time.iter().zip(store.kem_one_time.iter()) {
            assert_eq!(a.0, b.0, "kem one-time id");
            assert_eq!(a.1.public_key(), b.1.public_key(), "kem one-time key pair");
            assert_eq!(a.2, b.2, "kem one-time signature");
        }
        assert_eq!(restored.next_id, store.next_id);

        let original_bundle = store.publish();
        let restored_bundle = restored.publish();
        assert_eq!(
            original_bundle.signed_prekey_id,
            restored_bundle.signed_prekey_id
        );
        assert_eq!(
            original_bundle.one_time_prekey_id,
            restored_bundle.one_time_prekey_id
        );
        assert_eq!(original_bundle.kem_prekey_id, restored_bundle.kem_prekey_id);
        assert_eq!(
            original_bundle.bundle.identity_key,
            restored_bundle.bundle.identity_key
        );
        assert_eq!(
            original_bundle.bundle.signed_prekey,
            restored_bundle.bundle.signed_prekey
        );
        assert_eq!(
            original_bundle.bundle.kem_prekey,
            restored_bundle.bundle.kem_prekey
        );
    }

    /// A store with some one-time keys already consumed round-trips too --
    /// the shorter `Vec`s are the case a fresh store's test cannot reach.
    #[test]
    fn to_bytes_from_bytes_round_trips_a_partially_consumed_store() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let mut store = id.create_prekeys(4, &mut rng);
        let curve_id = store.one_time[0].0;
        let kem_id = store.kem_one_time[0].0;
        store.take_one_time(curve_id);
        store.take_one_time_kem(kem_id);
        assert_eq!(store.one_time.len(), 3);
        assert_eq!(store.kem_one_time.len(), 3);

        let bytes = store.to_bytes();
        let restored = PrekeyStore::from_bytes(&bytes).unwrap();
        assert_eq!(restored.one_time, store.one_time);
        assert_eq!(restored.kem_one_time.len(), store.kem_one_time.len());
        assert!(
            restored.one_time.iter().all(|(id, _)| *id != curve_id),
            "a consumed curve prekey came back on restore"
        );
        assert!(
            restored.kem_one_time.iter().all(|(id, _, _)| *id != kem_id),
            "a consumed KEM prekey came back on restore"
        );
    }

    /// The two private deletions preserve the store's invariant, and so does
    /// the removal shape they use (zeroize, swap-with-last, pop): the
    /// identifier the moved entry carries is still the one it had.
    #[test]
    fn the_one_time_deletions_preserve_the_invariant() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let mut store = id.create_prekeys(4, &mut rng);
        assert!(store.invariant());
        // Delete from the front, so the swap actually moves something.
        let curve_id = store.one_time[0].0;
        let kem_id = store.kem_one_time[0].0;
        assert!(store.take_one_time(curve_id));
        assert!(store.invariant());
        assert!(store.take_one_time_kem(kem_id).is_some());
        assert!(store.invariant());
        assert!(!store.take_one_time(curve_id), "already deleted");
        assert!(store.invariant());
    }

    /// A store with no one-time keys at all (the last-resort-only bundle
    /// case) round-trips too -- the empty end of the `Vec`s.
    #[test]
    fn to_bytes_from_bytes_round_trips_a_store_with_no_one_time_keys() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let store = id.create_prekeys(0, &mut rng);
        assert!(store.one_time.is_empty());
        assert!(store.kem_one_time.is_empty());

        let bytes = store.to_bytes();
        let restored = PrekeyStore::from_bytes(&bytes).unwrap();
        assert!(restored.one_time.is_empty());
        assert!(restored.kem_one_time.is_empty());
        assert_eq!(restored.kem.public_key(), store.kem.public_key());
    }

    #[test]
    fn prekey_store_from_bytes_rejects_a_foreign_version() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let store = id.create_prekeys(2, &mut rng);
        let mut bytes = store.to_bytes().to_vec();
        bytes[0] = 0xff;
        assert!(matches!(
            PrekeyStore::from_bytes(&bytes),
            Err(PrekeyStoreDecodeError::UnknownVersion)
        ));
    }

    /// A deterministic byte source, so a generated fixture is a property of
    /// *this code* rather than of whichever PRNG `rand` ships this month. The
    /// same reasoning as `primitives::xeddsa`'s.
    ///
    /// **Counter-based, where that one cycles a fixed buffer, and the
    /// difference is load-bearing.** A 64-byte cycle hands the same 32 bytes
    /// back for a later key, and a Diffie-Hellman ratchet step cannot tell such
    /// a key from the one it already holds: the session fixtures below could
    /// not complete a round trip at all until the stream stopped repeating
    /// (`NoReceivingChain` on the initiator's decrypt of the reply). The
    /// xeddsa source is fine for its own use, which draws one nonce and stops.
    ///
    /// The mixing is splitmix64, written out here rather than taken from a
    /// crate, for exactly the reason the stream is not `StdRng`'s: a fixture
    /// must not be hostage to a dependency's internals.
    struct FixedRng {
        seed: u64,
        at: u64,
    }

    impl rand_core::RngCore for FixedRng {
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
                let mut x = self
                    .at
                    .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    .wrapping_add(self.seed);
                x ^= x >> 30;
                x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
                x ^= x >> 27;
                x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
                x ^= x >> 31;
                *d = (x & 0xff) as u8;
                self.at = self.at.wrapping_add(1);
            }
        }
        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
            self.fill_bytes(dest);
            Ok(())
        }
    }
    impl rand_core::CryptoRng for FixedRng {}

    fn fixed_rng(seed: u8) -> FixedRng {
        FixedRng {
            seed: seed as u64,
            at: 0,
        }
    }

    /// Print the stored bytes of deterministic sessions, for the vector
    /// generator to carry as recorded inputs.
    ///
    /// Same reason as the prekey store's fixtures: the model cannot build a
    /// session whose `ratchet_private` matches the classical ratchet's
    /// `dhs_pub`, because it does not compute the curve. Three cases, chosen
    /// so the optional fields differ: an initiator nobody has answered yet
    /// (`pending_initial` present), a responder (`established_ephemeral`
    /// present), and an initiator whose peer has answered (neither).
    ///
    /// Ignored: it produces a fixture rather than checking anything.
    #[test]
    #[ignore = "prints a fixture; run with --ignored --nocapture"]
    fn print_session_fixtures() {
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        let mut rng = fixed_rng(0x37);
        let alice = Identity::from_secret([0x11u8; 32]);
        let bob = Identity::from_secret([0x22u8; 32]);
        let mut store = bob.create_prekeys(2, &mut rng);
        let bundle = store.publish();

        // An initiator that has sent its initial message and heard nothing.
        let mut initiator =
            establish_initiator(&alice, &bundle, &mut rng).expect("the bundle verifies");
        let first = initiator
            .encrypt(b"the first message", &mut rng)
            .expect("the initiator can send");
        let pending = initiator.export();
        assert!(Session::import(&pending).is_ok(), "the fixture must import");
        println!(
            "FIXTURE session-pending len={} hex={}",
            pending.len(),
            hex(&pending)
        );

        // The responder that answered it.
        let (mut responder, _) = establish_responder(&bob, &mut store, &first, &mut rng)
            .expect("the initial message authenticates");
        let responded = responder.export();
        assert!(
            Session::import(&responded).is_ok(),
            "the fixture must import"
        );
        println!(
            "FIXTURE session-responder len={} hex={}",
            responded.len(),
            hex(&responded)
        );

        // The initiator once the peer has answered, which drops pending_initial.
        let reply = responder
            .encrypt(b"the reply", &mut rng)
            .expect("the responder can send");
        let back = initiator
            .decrypt(&reply, &mut rng)
            .expect("the reply decrypts");
        assert_eq!(back, b"the reply");
        let answered = initiator.export();
        assert!(
            Session::import(&answered).is_ok(),
            "the fixture must import"
        );
        println!(
            "FIXTURE session-answered len={} hex={}",
            answered.len(),
            hex(&answered)
        );
    }

    /// Print the stored bytes of deterministic prekey stores, for the vector
    /// generator to carry as recorded inputs.
    ///
    /// The model cannot produce these: it has no signatures (see
    /// `Model.PersistedState.PrekeyStoreState`). An accepted prekey-store
    /// vector therefore takes its bytes from here, once, rather than from the
    /// generator. Refusal vectors need none of this and are generated in Lean,
    /// because the signature check runs last and a structurally refused store
    /// is refused for its structural reason by both readers.
    ///
    /// Ignored: it produces a fixture rather than checking anything.
    #[test]
    #[ignore = "prints a fixture; run with --ignored --nocapture"]
    fn print_prekey_store_fixtures() {
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        for (name, count) in [("no-one-time", 0usize), ("one-one-time", 1)] {
            let mut rng = fixed_rng(0x11);
            let id = Identity::from_secret([0x42u8; 32]);
            let store = id.create_prekeys(count, &mut rng);
            let bytes = store.to_bytes();
            assert!(
                PrekeyStore::from_bytes(&bytes).is_ok(),
                "the fixture must be one both readers accept"
            );
            println!("FIXTURE {name} len={} hex={}", bytes.len(), hex(&bytes));
        }
        // One with a retired pair, so the v3/v4 optional fields are exercised.
        let mut rng = fixed_rng(0x11);
        let id = Identity::from_secret([0x42u8; 32]);
        let mut store = id.create_prekeys(0, &mut rng);
        store.rotate_signed_prekey(&id, &mut rng);
        let bytes = store.to_bytes();
        assert!(PrekeyStore::from_bytes(&bytes).is_ok());
        println!(
            "FIXTURE retired-signed len={} hex={}",
            bytes.len(),
            hex(&bytes)
        );
    }

    /// The exact case external review reported: one byte of the current signed
    /// prekey's signature, at offset 69 of a v4 store.
    ///
    /// Written at the byte level rather than through the field, because the
    /// offset and the canonicality are half the finding: the flip survives the
    /// re-encode check, so nothing before the semantic rules can see it.
    /// Asserts both halves of what a mutation test owes -- that the import is
    /// refused, and what would have happened if it were not.
    #[test]
    fn prekey_store_refuses_a_corrupted_signed_prekey_signature() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let store = id.create_prekeys(2, &mut rng);
        let mut bytes = store.to_bytes().to_vec();
        // version(1) + identity_public(32) + signed_prekey_secret(32)
        // + signed_prekey_id(4) = 69, the first byte of signed_prekey_sig.
        bytes[69] ^= 0x01;

        // The flip is invisible to everything before the semantic rules.
        // Rebuilt through the decoder rather than cloned: `PrekeyStore` is
        // deliberately not `Clone`, because it holds secrets it erases on drop.
        let mut raw = PrekeyStore::from_bytes(&store.to_bytes()).expect("a genuine store restores");
        raw.signed_prekey_sig[0] ^= 0x01;
        assert_eq!(
            raw.to_bytes().to_vec(),
            bytes,
            "the flip must re-encode canonically, or it is a different test"
        );
        assert!(
            raw.invariant(),
            "the other five rules must still hold, or it is a different test"
        );

        // What the rule prevents.
        assert!(matches!(
            PrekeyStore::from_bytes(&bytes),
            Err(PrekeyStoreDecodeError::Incoherent)
        ));

        // And what would otherwise have happened: a bundle every initiator
        // refuses, emitted by a store that restored without complaint.
        assert!(matches!(
            crate::sessions::verify_bundle(&raw.publish().bundle),
            Err(crate::sessions::SessionError::BadSignedPrekeySignature)
        ));
    }

    /// The order of the two checks is the safety argument, so it is pinned.
    ///
    /// `signatures_verify` runs only after `invariant`, which is what bounds
    /// the verification work by a store the decoder has already accepted
    /// structurally (AUTHENTICATION-BOUNDARY.md). A store that breaks both a
    /// structural rule and a signature must therefore be refused as
    /// `Malformed`, not `Incoherent`: the cheap rule is reached first. Swap the
    /// two blocks in `from_bytes` and this is the test that goes red -- without
    /// it, the swap passes every other test in the tree.
    #[test]
    fn prekey_store_refuses_a_structural_break_before_a_signature_break() {
        let mut rng = fixed_rng(0x55);
        let id = Identity::from_secret([0x31u8; 32]);
        let mut store = id.create_prekeys(1, &mut rng);
        store.signed_prekey_sig[0] ^= 0x01; // the expensive rule
        store.kem_id = store.signed_prekey_id; // the cheap one: a repeated id
        assert!(
            !store.invariant(),
            "the structural rule must be the broken one"
        );
        assert!(
            matches!(
                PrekeyStore::from_bytes(&store.to_bytes()),
                Err(PrekeyStoreDecodeError::Malformed)
            ),
            "a store breaking both must be refused for the rule checked first"
        );
    }

    /// The signature rule binds every version the reader accepts, not only the
    /// one it writes.
    ///
    /// Scoping the check to `PREKEY_STORE_VERSION` restores the reported defect
    /// verbatim: the older layouts are byte-identical to v4 for a store with an
    /// empty replay record and nothing retired, so a corrupted v4 store
    /// relabelled v3 would import and publish an unusable bundle. Every other
    /// mutation test here uses a v4 store, so nothing else in the tree would
    /// notice.
    #[test]
    fn prekey_store_refuses_a_corrupted_signature_at_every_version_it_reads() {
        let mut rng = fixed_rng(0x56);
        let id = Identity::from_secret([0x32u8; 32]);
        let store = id.create_prekeys(0, &mut rng);
        let v4 = store.to_bytes().to_vec();
        // v4 ends `next_id(4) || seen_count(4)=0 || present(1)=0 || present(1)=0`.
        // v3 writes the same bytes when the record is empty and nothing is
        // retired; v2 has no retired fields; v1 has neither those nor a record.
        assert_eq!(
            &v4[v4.len() - 6..],
            &[0, 0, 0, 0, 0, 0],
            "empty record, nothing retired"
        );
        for (version, body) in [
            (PREKEY_STORE_VERSION_V3, &v4[1..]),
            (PREKEY_STORE_VERSION_V2, &v4[1..v4.len() - 2]),
            (PREKEY_STORE_VERSION_V1, &v4[1..v4.len() - 6]),
        ] {
            let mut bytes = vec![version];
            bytes.extend_from_slice(body);
            assert!(
                PrekeyStore::from_bytes(&bytes).is_ok(),
                "version {version:#04x} must restore before it is corrupted"
            );
            bytes[69] ^= 0x01;
            assert!(
                matches!(
                    PrekeyStore::from_bytes(&bytes),
                    Err(PrekeyStoreDecodeError::Incoherent)
                ),
                "version {version:#04x} with a corrupted signature must be refused"
            );
        }
    }

    /// The current KEM prekey's signature. Published on the last-resort path,
    /// once the one-time KEM prekeys are exhausted.
    #[test]
    fn prekey_store_refuses_a_corrupted_kem_signature() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let mut store = id.create_prekeys(0, &mut rng);
        store.kem_sig[0] ^= 0x01;
        assert!(store.invariant(), "only the signature is wrong");
        assert!(matches!(
            PrekeyStore::from_bytes(&store.to_bytes()),
            Err(PrekeyStoreDecodeError::Incoherent)
        ));
        assert!(matches!(
            crate::sessions::verify_bundle(&store.publish().bundle),
            Err(crate::sessions::SessionError::BadKemPrekeySignature)
        ));
    }

    /// A one-time KEM prekey's signature. Published in preference to the
    /// last-resort key, so this is the one a first contact actually meets.
    #[test]
    fn prekey_store_refuses_a_corrupted_one_time_kem_signature() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        // Every entry in turn, not one index. Corrupting only `last_mut()`
        // let a check narrowed to the last entry pass the whole tree: what
        // this pins is the loop, so it has to walk the loop.
        let count = 3;
        for i in 0..count {
            let mut store = id.create_prekeys(count, &mut rng);
            store.kem_one_time[i].2[0] ^= 0x01;
            assert!(store.invariant(), "only the signature is wrong");
            assert!(
                matches!(
                    PrekeyStore::from_bytes(&store.to_bytes()),
                    Err(PrekeyStoreDecodeError::Incoherent)
                ),
                "a corrupted signature on one-time KEM prekey {i} must be refused"
            );
        }
        // And the later failure, on the entry `publish` actually takes.
        let mut store = id.create_prekeys(count, &mut rng);
        store
            .kem_one_time
            .last_mut()
            .expect("a one-time KEM prekey")
            .2[0] ^= 0x01;
        assert!(matches!(
            crate::sessions::verify_bundle(&store.publish().bundle),
            Err(crate::sessions::SessionError::BadKemPrekeySignature)
        ));
    }

    /// The retired signed prekey's signature.
    ///
    /// No `verify_bundle` half here, deliberately: nothing reads a retired
    /// signature, so there is no later failure to demonstrate. The page says
    /// why it is checked anyway -- a retired signature was a current one, so one
    /// that no longer verifies is evidence the file was written to. Asserting a
    /// consequence this case does not have would be inventing one.
    #[test]
    fn prekey_store_refuses_a_corrupted_retired_signed_prekey_signature() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let mut store = id.create_prekeys(2, &mut rng);
        store.rotate_signed_prekey(&id, &mut rng);
        assert!(
            PrekeyStore::from_bytes(&store.to_bytes()).is_ok(),
            "the rotated store must restore before it is corrupted"
        );
        store
            .previous_signed_prekey
            .as_mut()
            .expect("a retired signed prekey")
            .2[0] ^= 0x01;
        assert!(store.invariant(), "only the signature is wrong");
        assert!(matches!(
            PrekeyStore::from_bytes(&store.to_bytes()),
            Err(PrekeyStoreDecodeError::Incoherent)
        ));
    }

    /// The retired KEM prekey's signature. Same reasoning as above.
    #[test]
    fn prekey_store_refuses_a_corrupted_retired_kem_signature() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let mut store = id.create_prekeys(2, &mut rng);
        store.rotate_kem(&id, &mut rng);
        assert!(
            PrekeyStore::from_bytes(&store.to_bytes()).is_ok(),
            "the rotated store must restore before it is corrupted"
        );
        store.previous_kem.as_mut().expect("a retired KEM prekey").2[0] ^= 0x01;
        assert!(store.invariant(), "only the signature is wrong");
        assert!(matches!(
            PrekeyStore::from_bytes(&store.to_bytes()),
            Err(PrekeyStoreDecodeError::Incoherent)
        ));
    }

    /// A genuine store restores. The control for the five above: without it
    /// they would all pass against a reader that refused everything.
    #[test]
    fn prekey_store_with_every_signature_intact_restores() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let mut store = id.create_prekeys(3, &mut rng);
        store.rotate_signed_prekey(&id, &mut rng);
        store.rotate_kem(&id, &mut rng);
        store.replenish(&id, 2, &mut rng);
        assert!(
            PrekeyStore::from_bytes(&store.to_bytes()).is_ok(),
            "a store whose every signature verifies must restore"
        );
    }

    /// The operations half of the rule: an operation handed the wrong identity
    /// changes nothing, rather than building a state the reader would refuse.
    #[test]
    fn prekey_operations_refuse_an_identity_that_is_not_the_stores() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let other = Identity::generate(&mut rng);
        assert_ne!(other.public(), id.public(), "the two identities differ");

        for (name, apply) in [
            (
                "rotate_signed_prekey",
                &(|s: &mut PrekeyStore, i: &Identity, r: &mut rand_core::OsRng| {
                    s.rotate_signed_prekey(i, r)
                }) as &dyn Fn(&mut PrekeyStore, &Identity, &mut rand_core::OsRng),
            ),
            ("rotate_kem", &|s, i, r| s.rotate_kem(i, r)),
            ("replenish", &|s, i, r| s.replenish(i, 2, r)),
        ] {
            let store = id.create_prekeys(2, &mut rng);
            let before = store.to_bytes().to_vec();

            let mut wrong = PrekeyStore::from_bytes(&before).expect("restores");
            apply(&mut wrong, &other, &mut rng);
            assert_eq!(
                wrong.to_bytes().to_vec(),
                before,
                "{name} under a foreign identity must change nothing"
            );

            // The same call under the store's own identity does change it, so
            // the assertion above is not passing because the call is inert.
            let mut right = PrekeyStore::from_bytes(&before).expect("restores");
            apply(&mut right, &id, &mut rng);
            assert_ne!(
                right.to_bytes().to_vec(),
                before,
                "{name} under the store's own identity must still work"
            );
            assert!(
                PrekeyStore::from_bytes(&right.to_bytes()).is_ok(),
                "{name} under the store's own identity must leave a readable store"
            );
        }
    }

    #[test]
    fn prekey_store_from_bytes_rejects_a_truncated_buffer() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let store = id.create_prekeys(2, &mut rng);
        let bytes = store.to_bytes();
        assert!(matches!(
            PrekeyStore::from_bytes(&bytes[..bytes.len() - 1]),
            Err(PrekeyStoreDecodeError::TooShort)
        ));
    }

    #[test]
    fn prekey_store_from_bytes_rejects_trailing_bytes() {
        let mut rng = rand_core::OsRng;
        let id = Identity::generate(&mut rng);
        let store = id.create_prekeys(2, &mut rng);
        let mut bytes = store.to_bytes().to_vec();
        bytes.push(0x00);
        assert!(matches!(
            PrekeyStore::from_bytes(&bytes),
            Err(PrekeyStoreDecodeError::Malformed)
        ));
    }

    /// A restored identity is the same identity: same public key, and a
    /// signature it makes verifies under the original's published key.
    #[test]
    fn an_identity_survives_export() {
        let mut rng = rand_core::OsRng;
        let a = Identity::generate(&mut rng);
        let restored = Identity::from_secret(*a.export());

        assert_eq!(a.public().as_bytes(), restored.public().as_bytes());

        let challenge = b"a server-issued challenge";
        let sig = restored.sign_message(challenge, &mut rng);
        assert!(super::super::verify_under_identity(
            &a.public(),
            challenge,
            &sig
        ));
    }

    /// A signature verifies under its own identity and nothing else.
    #[test]
    fn a_challenge_signature_binds_to_its_identity() {
        let mut rng = rand_core::OsRng;
        let a = Identity::generate(&mut rng);
        let b = Identity::generate(&mut rng);
        let challenge = b"a server-issued challenge";
        let sig = a.sign_message(challenge, &mut rng);

        assert!(super::super::verify_under_identity(
            &a.public(),
            challenge,
            &sig
        ));
        assert!(!super::super::verify_under_identity(
            &b.public(),
            challenge,
            &sig
        ));
        assert!(!super::super::verify_under_identity(
            &a.public(),
            b"another",
            &sig
        ));

        let mut tampered = sig;
        tampered[0] ^= 0x01;
        assert!(!super::super::verify_under_identity(
            &a.public(),
            challenge,
            &tampered
        ));
    }
}
