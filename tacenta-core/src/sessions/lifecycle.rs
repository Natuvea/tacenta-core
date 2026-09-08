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
    initiator_shared_secret, responder_shared_secret,
};
use tacenta_spqr::SpqrError;
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
    /// identity by signing it. Verified with [`verify_under_identity`].
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
    pub fn create_prekeys<R: RngCore + CryptoRng>(
        &self,
        one_time_count: usize,
        rng: &mut R,
    ) -> PrekeyStore {
        // Identifiers start at one because zero is the absent-identifier
        // sentinel. The counter is returned in the store so that replenishment
        // continues from here; see `PrekeyStore::next_id`.
        let mut next_id: u32 = 1;
        let mut fresh_id = || {
            let id = next_id;
            next_id += 1;
            id
        };

        let signed_prekey_secret = random_secret(rng);
        let signed_prekey_id = fresh_id();
        let signed_prekey_pub = dh::PrivateKey::from_bytes(signed_prekey_secret).public_key();
        let signed_prekey_sig = self.sign(&encode_ec(&signed_prekey_pub), rng);

        let one_time = (0..one_time_count)
            .map(|_| (fresh_id(), random_secret(rng)))
            .collect();

        let kem = kem::KeyPair::generate(rng);
        let kem_id = fresh_id();
        let kem_sig = self.sign(&encode_kem(&kem.public_key()), rng);

        // Every KEM prekey is signed individually, unlike the one-time curve
        // prekeys, which are not signed at all. That asymmetry is the
        // specification's, not ours.
        let kem_one_time = (0..one_time_count)
            .map(|_| {
                let pair = kem::KeyPair::generate(rng);
                let sig = self.sign(&encode_kem(&pair.public_key()), rng);
                (fresh_id(), pair, sig)
            })
            .collect();

        PrekeyStore {
            next_id,
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

/// How many spent last-resort handshakes a store remembers.
///
/// 1024 fingerprints is 32 KB, which is small beside a single 14 KB session
/// and generous beside the number of peers that should ever reach the
/// last-resort path at all -- they only do so once one-time KEM prekeys are
/// exhausted. Chosen to be comfortably larger than any realistic burst rather
/// than tuned; the note on `PrekeyStore::last_resort_seen` says what is given
/// up by having a bound at all.
const MAX_LAST_RESORT_SEEN: usize = 1024;

/// A domain-separated fingerprint of the handshake half of an initial message.
///
/// It covers exactly the fields that determine `SK`: both public keys, the KEM
/// ciphertext, and the two prekey identifiers. The ratchet message is left out
/// on purpose -- it is authenticated under keys derived from `SK`, so an
/// attacker cannot vary it and still be accepted, and including it would let a
/// replay evade the check by being re-framed.
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
    /// same terms. The last-resort fingerprints below are not rotated with
    /// it: a replay against the previous key is still a replay.
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
    /// Today nothing can produce a duplicate: `create_prekeys` numbers a whole
    /// store in one pass and is the only thing that builds one. But one-time
    /// keys are consumed and will need replenishing, and the obvious way to
    /// write that is to call `create_prekeys` again and combine the results --
    /// at which point the identifiers restart at one and collide. This field
    /// exists so that replenishment has somewhere correct to continue from, and
    /// so the requirement is visible to whoever writes it rather than
    /// rediscovered.
    next_id: u32,
    /// Fingerprints of last-resort handshakes this store has already accepted,
    /// newest last, capped at `MAX_LAST_RESORT_SEEN`.
    ///
    /// **What this is for.** A one-time KEM prekey defends itself: it is
    /// deleted on use, so replaying an initial message that names one fails
    /// with `UnknownPrekeyId`. The last-resort key is reusable by design and
    /// has no such defence, so without this field a captured initial message
    /// could be replayed without limit, each replay opening a *fresh duplicate
    /// session*. No content leaks -- the attacker learns nothing and the
    /// session is one they cannot speak on -- but unbounded session creation
    /// from one captured packet is a denial of service, and the sessions are
    /// 14 KB each on disk.
    ///
    /// The specification is aware that the handshake replays: without a
    /// one-time *curve* prekey Bob derives the same `SK` in different runs,
    /// which is why the ratchet must randomise before he replies
    /// (session-establishment.md, "Replay, and why the ratchet must follow").
    /// That reasoning is about key reuse. It says nothing about how many
    /// sessions the replay may create, which is what this bounds.
    ///
    /// **The bound is a real limit, not a formality.** Past
    /// `MAX_LAST_RESORT_SEEN` distinct last-resort handshakes the oldest
    /// fingerprint is evicted and a replay of *that* one would be accepted
    /// again. The alternative is an unbounded set, which is the same denial of
    /// service wearing different clothes. Keeping one-time KEM prekeys stocked
    /// (`replenish`) is what keeps the last-resort path rare enough for the
    /// bound to be generous; this field is the backstop for when it is not.
    last_resort_seen: Vec<[u8; 32]>,
}

/// Erased on drop, by hand rather than by derive.
///
/// The derive cannot reach the two collections: `zeroize` implements `Zeroize`
/// for `Vec<Z> where Z: Zeroize` but not for tuples, and both one-time
/// collections are vectors of tuples. Writing the destructor out covers them,
/// and it is the same answer `tacenta_spqr::State` already gives for the same
/// reason one crate over.
///
/// The KEM key pairs are not touched here and do not need to be: `kem::KeyPair`
/// erases itself, so dropping the vectors that hold them wipes them. The
/// identifiers, the identity's *public* key, and the signatures are public and
/// are left alone.
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
    pub fn replenish<R: RngCore + CryptoRng>(
        &mut self,
        identity: &Identity,
        count: usize,
        rng: &mut R,
    ) {
        // The identifier space is finite, and wrapping it would reach the
        // absent-identifier sentinel and then collide with live entries, the
        // exact trap `next_id`'s own note describes. Unreachable in any real
        // store, so it is refused quietly rather than panicked on: a store
        // that has issued four billion identifiers stops issuing them.
        for _ in 0..count {
            let Some(next) = self.next_id.checked_add(1) else {
                return;
            };
            let id = self.next_id;
            self.next_id = next;
            self.one_time.push((id, random_secret(rng)));
        }
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
    pub fn rotate_signed_prekey<R: RngCore + CryptoRng>(
        &mut self,
        identity: &Identity,
        rng: &mut R,
    ) {
        let Some(next) = self.next_id.checked_add(1) else {
            return;
        };
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
    /// it. The fingerprints of spent last-resort handshakes are kept across
    /// the rotation; a replay against the retired key is still a replay.
    pub fn rotate_kem<R: RngCore + CryptoRng>(&mut self, identity: &Identity, rng: &mut R) {
        let Some(next) = self.next_id.checked_add(1) else {
            return;
        };
        let pair = kem::KeyPair::generate(rng);
        let id = self.next_id;
        self.next_id = next;
        let sig = identity.sign(&encode_kem(&pair.public_key()), rng);
        let retired = core::mem::replace(&mut self.kem, pair);
        // `kem::KeyPair` erases itself, so the older previous needs no help.
        self.previous_kem = Some((retired, self.kem_id, self.kem_sig));
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
    /// The vacated slot at the end of the vector afterwards holds a
    /// copy of whichever live entry `swap_remove` moved, which is the same
    /// exposure as the live entry itself and is wiped with it on drop.
    fn take_one_time(&mut self, id: u32) -> bool {
        match self.one_time.iter().position(|(k, _)| *k == id) {
            Some(i) => {
                self.one_time[i].1.zeroize();
                self.one_time.swap_remove(i);
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
    fn take_one_time_kem(&mut self, id: u32) -> Option<kem::KeyPair> {
        let i = self.kem_one_time.iter().position(|(k, _, _)| *k == id)?;
        let (_, pair, _) = self.kem_one_time.swap_remove(i);
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
            + self.last_resort_seen.len() * 32
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

        out.extend_from_slice(&(self.last_resort_seen.len() as u32).to_be_bytes());
        for fp in &self.last_resort_seen {
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
    pub fn from_bytes(bytes: &[u8]) -> Result<PrekeyStore, PrekeyStoreDecodeError> {
        if bytes.is_empty() {
            return Err(PrekeyStoreDecodeError::TooShort);
        }
        let version = bytes[0];
        if version != PREKEY_STORE_VERSION
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
        let mut one_time = Vec::new();
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
        let mut kem_one_time = Vec::new();
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
            // trusting it to size anything.
            if seen_count as usize > MAX_LAST_RESORT_SEEN {
                return Err(PrekeyStoreDecodeError::Malformed);
            }
            for _ in 0..seen_count {
                if bytes.len() < pos + 32 {
                    return Err(PrekeyStoreDecodeError::TooShort);
                }
                let mut fp = [0u8; 32];
                fp.copy_from_slice(&bytes[pos..pos + 32]);
                pos += 32;
                last_resort_seen.push(fp);
            }
        }

        // A v1 or v2 store predates rotation and has retired nothing.
        let mut previous_signed_prekey = None;
        let mut previous_kem = None;
        if version == PREKEY_STORE_VERSION {
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

        Ok(PrekeyStore {
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
        })
    }
}

/// This module's own persistence-format version for `PrekeyStore::to_bytes`/
/// `from_bytes`, separate from any on-the-wire message version.
/// The version `to_bytes` writes. `from_bytes` also accepts
/// `PREKEY_STORE_VERSION_V1`, which is the same format without the
/// last-resort fingerprints; such a store reads back with none remembered,
/// which is the honest answer -- it never recorded any.
const PREKEY_STORE_VERSION: u8 = 0x03;
/// The format before prekey rotation: v2 without the
/// two retired-prekey fields. Reads back with nothing retired.
const PREKEY_STORE_VERSION_V2: u8 = 0x02;
/// The format before last-resort replay marking.
const PREKEY_STORE_VERSION_V1: u8 = 0x01;

/// A `PrekeyStore::to_bytes`/`from_bytes` failure. As with `Session`'s own
/// `SessionDecodeError`, the threat model is corruption and version skew,
/// not a hostile peer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PrekeyStoreDecodeError {
    UnknownVersion,
    TooShort,
    Malformed,
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
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    /// The composition refused: either ratchet may be the reason, and the
    /// variant carries which.
    Triple(tacenta_triple::TripleError),
    /// A prekey signature in the bundle did not verify.
    Handshake(SessionError),
    /// A KEM public key or ciphertext was malformed.
    Kem,
    /// A message did not decode.
    Decode(DecodeError),
    /// A curve public key on the wire was not a recognised encoding.
    BadEncoding,
    /// An identifier named a prekey the store does not hold.
    UnknownPrekeyId,
    /// The AEAD did not authenticate.
    Aead,
    /// The ratchet rejected the step.
    Ratchet(ratchet::RatchetError),
    /// An initial message arrived on an established session and is not a repeat
    /// of the one that established it. Opening a session is
    /// `establish_responder`'s job, and doing it here would discard this one.
    NotARepeatedInitial,
    /// A last-resort handshake this store has already accepted arrived again.
    ///
    /// Distinct from `NotARepeatedInitial`, which is about a *session* that
    /// already exists. This one fires before any session does: the initial
    /// message names the reusable last-resort KEM key, and its fingerprint
    /// matches one already spent. See `last_resort_seen`.
    ReplayedLastResort,
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
pub fn establish_initiator<R: RngCore + CryptoRng>(
    our_identity: &Identity,
    their_bundle: &PublishedBundle,
    rng: &mut R,
) -> Result<Session, Error> {
    let bundle = &their_bundle.bundle;
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
    let dh_out = ratchet_private
        .agree(&peer_signed_prekey)
        .ok_or(Error::Handshake(SessionError::NonContributoryAgreement))?;
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
/// what a crash between the two costs.
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
    let signed_prekey_secret: Zeroizing<[u8; 32]> = Zeroizing::new(
        if decoded.signed_prekey_id == our_prekeys.signed_prekey_id {
            our_prekeys.signed_prekey_secret
        } else if let Some((secret, id, _)) = &our_prekeys.previous_signed_prekey
            && *id == decoded.signed_prekey_id
        {
            *secret
        } else {
            return Err(Error::UnknownPrekeyId);
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
    if let Some(fp) = &fingerprint
        && our_prekeys.last_resort_seen.contains(fp)
    {
        return Err(Error::ReplayedLastResort);
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
    // A last-resort handshake cannot be deleted, so it is remembered instead.
    // Oldest evicted first: see the bound's note on the field.
    if let Some(fp) = fingerprint {
        if our_prekeys.last_resort_seen.len() >= MAX_LAST_RESORT_SEEN {
            our_prekeys.last_resort_seen.remove(0);
        }
        our_prekeys.last_resort_seen.push(fp);
    }
    Ok((session, plaintext))
}

impl Session {
    /// Encrypt a message.
    ///
    /// An initiator prepends the initial (prekey) message to **every** message
    /// until the peer answers, as the Double Ratchet specification recommends:
    /// an initial message sent only once can be lost or reordered, leaving the
    /// peer with no session and every later message undecryptable. The
    /// conformance suite exercises this by asking a responder to read a third
    /// message first.
    /// Whether the post-quantum key agreement has reached its terminal failure
    /// state. Once true, `encrypt` and `decrypt` return
    /// [`Error::AgreementFailed`]; the session must be re-established.
    pub fn agreement_failed(&self) -> bool {
        self.braid.failed()
    }

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
    pub fn decrypt<R: RngCore + CryptoRng>(
        &mut self,
        message: &[u8],
        rng: &mut R,
    ) -> Result<Vec<u8>, Error> {
        let inner = match message_type(message) {
            Some(MessageType::Initial) => {
                let decoded = decode_initial(message).map_err(Error::Decode)?;
                match self.established_ephemeral.as_ref() {
                    Some(e) if *e == decoded.ephemeral => decoded.message,
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
        let dh_out_recv = self.ratchet_private.agree(&peer).ok_or(nc)?;
        let candidate_key = dh::PrivateKey::from_bytes(random_secret(rng));
        let dh_out_send = candidate_key.agree(&peer).ok_or(nc)?;

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
        // Evictions grow geometrically within one store, so a message that
        // needs many slots costs a handful of attempts rather than one per
        // slot, and the batch starts again at one when the *other* store
        // reports full: the classical half runs first inside `receive`, so a
        // batch inflated by its rounds must not be spent on the post-quantum
        // store, whose need is unrelated.
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
                let mut batch: usize = 1;
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
                    // an eviction returns zero.
                    batch *= 2;
                    match receive(&work) {
                        Ok(v) => break v,
                        Err(e) => {
                            let Some(next) = full_store(&e) else {
                                return Err(Error::Triple(e));
                            };
                            if next != half {
                                half = next;
                                batch = 1;
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
    /// **What it does not catch**: a byte string that is canonical and
    /// semantically extreme. A saturated counter re-encodes to itself and
    /// passes. That is a separate property whose check belongs at the use
    /// site, not here.
    pub fn import(bytes: &[u8]) -> Result<Session, SessionDecodeError> {
        let session = Session::import_unchecked(bytes)?;
        if session.export().as_slice() != bytes {
            return Err(SessionDecodeError::NonCanonical);
        }
        Ok(session)
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

        store.rotate_kem(&bob, &mut rng);
        let mut s2 = establish_initiator(&alice, &before, &mut rng).unwrap();
        let m2 = s2.encrypt(b"gone", &mut rng).unwrap();
        assert!(matches!(
            establish_responder(&bob, &mut store, &m2, &mut rng),
            Err(Error::UnknownPrekeyId)
        ));
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

        // Truncating the v3 tail and relabelling as v2 is exactly a v2 store.
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
    /// `PrekeyStore` by a hand-written destructor, since `zeroize` has no
    /// `Zeroize` for tuples and both one-time collections are vectors of them --
    /// so there is nothing in the type declarations for a reader to notice.
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
