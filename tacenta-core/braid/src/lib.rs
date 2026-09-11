//! tacenta-braid: the ML-KEM Braid, a sparse continuous key agreement.
//!
//! Written from tacenta-spec/protocol/mlkem-braid.md and the executable model
//! in tacenta-model (`Model.Braid`), not from any implementation's source.
//!
//! Two parties who can only exchange small messages produce a sequence of
//! post-quantum shared secrets, one per epoch. The values involved are far too
//! large to send whole, so each travels as an erasure-coded stream of codewords,
//! and ML-KEM's ciphertext is split at the point where its halves stop depending
//! on each other so both sides can transmit at once. That overlap is what the
//! protocol is named for.
//!
//! ## The shape of the API
//!
//! Eleven states, and the caller never names one. It calls [`Braid::send`] when
//! it has a message going out and [`Braid::receive`] when one arrives, and the
//! machine advances itself.
//!
//! Both report an epoch, and both sometimes yield a key. The epoch reported is
//! **the latest one both parties are known to hold**, which is not the one being
//! negotiated and is not always the one a key was just emitted for. The
//! responder learns an epoch's key several messages before the initiator does,
//! and these values are how a caller above knows which keys it may safely use.
//! `Model.Braid` proves that the two sides label the same key with the same
//! number, which is the part of this that is easy to get wrong.
//!
//! ## Failure is terminal
//!
//! A MAC that does not verify, or an `ek_vector` that does not match the header
//! it was promised by, abandons the session. The published specification says to
//! negotiate a new one, and the private `Failed` state, reported through
//! [`Braid::failed`], makes that unrepresentable otherwise rather than leaving
//! it to a caller's discipline. See the
//! implementation decisions on the specification page for why that matters
//! here: the
//! authenticator has already ratcheted by the time the ciphertext MAC is
//! checked, because the MAC key is what the ratchet produced.

#![forbid(unsafe_code)]
// No `?`: `let`-`else` and `match` instead, for the reason recorded once in
// tacenta-ratchet's module doc ("The `?` operator"). The lint asks for `?`.
#![allow(clippy::question_mark)]
// Every `Receive` in the published pseudocode tests the epoch and message type
// first and then looks at the payload, and this file keeps that shape so the
// correspondence can be checked by eye. Collapsing the two would read better to
// a linter and worse to a reviewer holding the specification.
#![allow(clippy::collapsible_if)]

use rand_core::{CryptoRng, RngCore};
use tacenta_erasure::{CHUNK_BYTES, Chunk, Decoder, Encoder, chunk_count};
use tacenta_kem::{
    CT1_LEN, CT2_LEN, EK_VECTOR_LEN, EncapsState, HEADER_LEN, IncrementalKeyPair, encapsulate1,
    encapsulate2, validate_ek,
};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

/// The MAC's output length.
pub const MAC_LEN: usize = 32;

/// `PROTOCOL_INFO`: the protocol, the KEM, and the MAC.
///
/// Wire-sensitive. Recorded in the conformance manifest rather than settled
/// here, on the same footing as every other constant that has to match a peer.
const PROTOCOL_INFO: &[u8] = b"Tacenta_MLKEM1024_SHA-256";

const AUTH_UPDATE: &[u8] = b":Authenticator Update";
const SCKA_KEY: &[u8] = b":SCKA Key";
const EK_HEADER: &[u8] = b":ekheader";
const CIPHERTEXT: &[u8] = b":ciphertext";

/// A key the agreement produced, with the epoch it belongs to.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct Output {
    #[zeroize(skip)]
    pub key_epoch: u64,
    pub key: [u8; 32],
}

// Test-only, for two reasons. It does not translate -- Aeneas cannot follow a
// `debug_struct` -- and **`Output` carries a key**, so the absence of a `Debug`
// in a shipping build is a compile-time guard: a `#[derive(Debug)]` on anything
// containing one will not compile rather than quietly printing it. The impl
// below exists so tests can name the type, and it prints the epoch only.
#[cfg(test)]
impl core::fmt::Debug for Output {
    /// Prints the epoch and not the key.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Output")
            .field("key_epoch", &self.key_epoch)
            .finish_non_exhaustive()
    }
}

/// What a message carries.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MsgType {
    /// Nothing to send this turn.
    None,
    /// Part of the header.
    Hdr,
    /// Part of `ek_vector`.
    Ek,
    /// Part of `ek_vector`, and `ct1` arrived in full.
    EkCt1Ack,
    /// Part of `ct1`.
    Ct1,
    /// Part of `ct2`.
    Ct2,
}

/// One message of the agreement, to be carried inside whatever the layer above
/// sends.
///
/// The specification's message enum has a seventh member, `Ct1Ack`, which
/// acknowledges `ct1` with no payload attached. No state produces it: the
/// acknowledgement always rides on an `ek_vector` chunk, because the sender
/// never learns that `ek_vector` has been fully received and so never runs out
/// of chunks to attach it to. It is absent here rather than present and dead, so
/// that a peer emitting one fails to parse instead of being ignored without
/// notice.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Msg {
    pub epoch: u64,
    pub ty: MsgType,
    pub data: Option<Chunk>,
}

impl Msg {
    fn empty(epoch: u64) -> Msg {
        Msg {
            epoch,
            ty: MsgType::None,
            data: None,
        }
    }

    fn with(epoch: u64, ty: MsgType, chunk: Option<Chunk>) -> Msg {
        match chunk {
            Some(c) => Msg {
                epoch,
                ty,
                data: Some(c),
            },
            // A stream that has produced all 65536 of the field's codewords has
            // nothing left to say. Unreachable in practice: the largest value
            // here is 48 codewords.
            None => Msg::empty(epoch),
        }
    }
}

/// The Ratcheted Authenticator: the agreement's own message authentication,
/// independent of whatever the layer above provides.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct Auth {
    root_key: [u8; 32],
    mac_key: [u8; 32],
}

/// `PROTOCOL_INFO || label || ToBytes(epoch)`, the shape every derivation here
/// takes. Epochs are big-endian, as the specification recommends.
fn info(label: &[u8], epoch: u64) -> Vec<u8> {
    let mut out = Vec::with_capacity(PROTOCOL_INFO.len() + label.len() + 8);
    out.extend_from_slice(PROTOCOL_INFO);
    out.extend_from_slice(label);
    out.extend_from_slice(&epoch.to_be_bytes());
    out
}

impl Auth {
    /// An authenticator with a given root key and no MAC key yet.
    ///
    /// For conformance checking against the model's vectors, which supply a
    /// root key directly rather than deriving one. Compiled only for this
    /// crate's tests and for the vectors runner, which enables the
    /// `conformance` feature. The gate keeps an API a shipping build has no
    /// use for out of its surface; it removes no capability, since
    /// `from_bytes` restores an authenticator, keys and all, from a persisted
    /// Braid (CR-22).
    #[cfg(any(test, feature = "conformance"))]
    pub fn from_root(root_key: [u8; 32]) -> Auth {
        Auth {
            root_key,
            mac_key: [0u8; 32],
        }
    }

    /// The two keys, for conformance checking. They are secret, so this is
    /// compiled only where `from_root` is. As there, the gate is about the
    /// API, not the capability: `to_bytes` carries both keys in the clear for
    /// persistence, so whoever holds the Braid can already read them.
    #[cfg(any(test, feature = "conformance"))]
    pub fn keys(&self) -> ([u8; 32], [u8; 32]) {
        (self.root_key, self.mac_key)
    }

    /// Start from a zero root key and immediately absorb the preshared secret.
    pub fn init(epoch: u64, secret: &[u8]) -> Auth {
        let mut a = Auth {
            root_key: [0u8; 32],
            mac_key: [0u8; 32],
        };
        a.update(epoch, secret);
        a
    }

    /// Absorb new entropy: 64 bytes of HKDF split into a new root and a new MAC
    /// key.
    pub fn update(&mut self, epoch: u64, key: &[u8]) {
        // Wiped on the way out, as the ratchet's `kdf_rk` wipes its own: the
        // 64 bytes hold both keys.
        let out = Zeroizing::new(tacenta_kdf::hkdf_sha256::<64>(
            &self.root_key,
            key,
            &info(AUTH_UPDATE, epoch),
        ));
        self.root_key.copy_from_slice(&out[..32]);
        self.mac_key.copy_from_slice(&out[32..]);
    }

    fn mac_hdr(&self, epoch: u64, hdr: &[u8]) -> [u8; MAC_LEN] {
        let mut data = info(EK_HEADER, epoch);
        data.extend_from_slice(hdr);
        tacenta_kdf::hmac_sha256(&self.mac_key, &data)
    }

    fn mac_ct(&self, epoch: u64, ct1: &[u8], ct2: &[u8]) -> [u8; MAC_LEN] {
        let mut data = info(CIPHERTEXT, epoch);
        data.extend_from_slice(ct1);
        data.extend_from_slice(ct2);
        tacenta_kdf::hmac_sha256(&self.mac_key, &data)
    }
}

/// The epoch key, derived from the raw shared secret before anything uses it.
///
/// Public so the vectors generated from `Model.Braid` can be checked against
/// it. This derivation carries `PROTOCOL_INFO`, and a vector pins this
/// constant against the model.
pub fn kdf_ok(shared_secret: &[u8], epoch: u64) -> [u8; 32] {
    tacenta_kdf::hkdf_sha256(&[0u8; 32], shared_secret, &info(SCKA_KEY, epoch))
}

/// Constant-time equality for MACs.
///
/// The comparison is over a value an attacker supplies against one derived from
/// a key they do not have; a timing leak would say whether a forgery got
/// closer, so the comparison accumulates every byte and never short-circuits.
fn mac_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff: u8 = 0;
    let mut i = 0;
    while i < a.len() {
        diff |= a[i] ^ b[i];
        i += 1;
    }
    diff == 0
}

/// Which of the eleven states the machine is in, plus the terminal one.
///
/// Private, contents and all: the variants carry decapsulation keys and
/// encapsulation state. A caller observes failure through `Braid::failed` and
/// progress through `Braid::state_tag` and `Braid::epoch`.
#[allow(clippy::large_enum_variant)]
#[derive(Clone)]
enum State {
    KeysUnsampled {
        epoch: u64,
        auth: Auth,
    },
    KeysSampled {
        epoch: u64,
        auth: Auth,
        kp: IncrementalKeyPair,
        hdr_enc: Encoder,
    },
    HeaderSent {
        epoch: u64,
        auth: Auth,
        kp: IncrementalKeyPair,
        ct1_dec: Decoder,
        ek_enc: Encoder,
    },
    Ct1Received {
        epoch: u64,
        auth: Auth,
        kp: IncrementalKeyPair,
        ct1: Vec<u8>,
        ek_enc: Encoder,
    },
    EkSentCt1Received {
        epoch: u64,
        auth: Auth,
        kp: IncrementalKeyPair,
        ct1: Vec<u8>,
        ct2_dec: Decoder,
    },
    NoHeaderReceived {
        epoch: u64,
        auth: Auth,
        hdr_dec: Decoder,
    },
    HeaderReceived {
        epoch: u64,
        auth: Auth,
        header: Vec<u8>,
        ek_dec: Decoder,
    },
    Ct1Sampled {
        epoch: u64,
        auth: Auth,
        header: Vec<u8>,
        encaps: EncapsState,
        ct1: Vec<u8>,
        ct1_enc: Encoder,
        ek_dec: Decoder,
    },
    EkReceivedCt1Sampled {
        epoch: u64,
        auth: Auth,
        encaps: EncapsState,
        ct1: Vec<u8>,
        ek_vector: Vec<u8>,
        ct1_enc: Encoder,
    },
    Ct1Acknowledged {
        epoch: u64,
        auth: Auth,
        header: Vec<u8>,
        encaps: EncapsState,
        ct1: Vec<u8>,
        ek_dec: Decoder,
    },
    Ct2Sampled {
        epoch: u64,
        auth: Auth,
        ct2_enc: Encoder,
    },
    Failed,
}

impl State {
    fn epoch(&self) -> u64 {
        match self {
            State::KeysUnsampled { epoch, .. }
            | State::KeysSampled { epoch, .. }
            | State::HeaderSent { epoch, .. }
            | State::Ct1Received { epoch, .. }
            | State::EkSentCt1Received { epoch, .. }
            | State::NoHeaderReceived { epoch, .. }
            | State::HeaderReceived { epoch, .. }
            | State::Ct1Sampled { epoch, .. }
            | State::EkReceivedCt1Sampled { epoch, .. }
            | State::Ct1Acknowledged { epoch, .. }
            | State::Ct2Sampled { epoch, .. } => *epoch,
            State::Failed => 0,
        }
    }

    /// A name for the state, for tests and diagnostics. Carries no secret.
    /// Test-only: selecting between `&'static str` constants is outside the
    /// translatable subset, the same limitation the translation notes in
    /// `tacenta-proofs/upstream/README.md` record for `&'static [u8]`. Nothing
    /// outside the tests asks a state its name.
    #[cfg(test)]
    fn name(&self) -> &'static str {
        match self {
            State::KeysUnsampled { .. } => "KeysUnsampled",
            State::KeysSampled { .. } => "KeysSampled",
            State::HeaderSent { .. } => "HeaderSent",
            State::Ct1Received { .. } => "Ct1Received",
            State::EkSentCt1Received { .. } => "EkSentCt1Received",
            State::NoHeaderReceived { .. } => "NoHeaderReceived",
            State::HeaderReceived { .. } => "HeaderReceived",
            State::Ct1Sampled { .. } => "Ct1Sampled",
            State::EkReceivedCt1Sampled { .. } => "EkReceivedCt1Sampled",
            State::Ct1Acknowledged { .. } => "Ct1Acknowledged",
            State::Ct2Sampled { .. } => "Ct2Sampled",
            State::Failed => "Failed",
        }
    }
}

/// One party's half of an ML-KEM Braid.
///
/// `Clone`, so a received message can advance a copy that is adopted only once
/// the message authenticates. A message touches three state machines, this
/// agreement and both ratchets, and all three roll back together.
///
/// Cloning is ordinary here: the erasure coders derive `Clone`, and the
/// incremental ML-KEM key pair is a boxed byte array.
///
/// What it does cost is real: the widest state carries an incremental key pair
/// of nearly twelve kilobytes, copied per received message and wiped when the
/// loser drops. Worth it to make a forged message unable to move the agreement.
#[derive(Clone)]
pub struct Braid {
    state: State,
}

fn hdr_decoder() -> Decoder {
    Decoder::new(HEADER_LEN + MAC_LEN)
}

impl Braid {
    /// The party that sends an encapsulation key first.
    pub fn initiator(secret: &[u8]) -> Braid {
        Braid {
            state: State::KeysUnsampled {
                epoch: 1,
                auth: Auth::init(1, secret),
            },
        }
    }

    /// The party that waits for one.
    pub fn responder(secret: &[u8]) -> Braid {
        Braid {
            state: State::NoHeaderReceived {
                epoch: 1,
                auth: Auth::init(1, secret),
                hdr_dec: hdr_decoder(),
            },
        }
    }

    /// The epoch currently being negotiated.
    pub fn epoch(&self) -> u64 {
        self.state.epoch()
    }

    /// Whether the session has been abandoned. Nothing leaves this.
    pub fn failed(&self) -> bool {
        matches!(self.state, State::Failed)
    }

    /// A stable number for the state, for a caller that needs to observe
    /// whether the machine moved. For tests and diagnostics; carries no secret.
    ///
    /// A number rather than a name because selecting between `&'static str`
    /// constants is outside the translatable subset, and this crate is a
    /// verified zone now. Callers compare tags; nothing formats them. The
    /// readable version below is test-only and stays that way.
    pub fn state_tag(&self) -> u8 {
        match self.state {
            State::KeysUnsampled { .. } => 0,
            State::KeysSampled { .. } => 1,
            State::HeaderSent { .. } => 2,
            State::Ct1Received { .. } => 3,
            State::EkSentCt1Received { .. } => 4,
            State::NoHeaderReceived { .. } => 5,
            State::HeaderReceived { .. } => 6,
            State::Ct1Sampled { .. } => 7,
            State::EkReceivedCt1Sampled { .. } => 8,
            State::Ct1Acknowledged { .. } => 9,
            State::Ct2Sampled { .. } => 10,
            State::Failed => 11,
        }
    }

    /// Test-only, for the same reason as `State::name`.
    #[cfg(test)]
    pub fn state_name(&self) -> &'static str {
        self.state.name()
    }

    /// Which party this is: `Some(true)` for the one `initiator` built,
    /// `Some(false)` for `responder`'s, and `None` once the session has
    /// failed. Not stored. The variant says which side of the current epoch
    /// this party is on -- the five states that send a header or the six
    /// that wait for one -- and the sides swap each epoch (transitions (5)
    /// and (13)), so the party that started as initiator is on the
    /// header-sending side in every odd epoch and on the other in every even
    /// one. For a caller above checking that its own record of the role
    /// agrees with the agreement's.
    pub fn is_initiator(&self) -> Option<bool> {
        let sends_header = match self.state {
            State::KeysUnsampled { .. }
            | State::KeysSampled { .. }
            | State::HeaderSent { .. }
            | State::Ct1Received { .. }
            | State::EkSentCt1Received { .. } => true,
            State::NoHeaderReceived { .. }
            | State::HeaderReceived { .. }
            | State::Ct1Sampled { .. }
            | State::EkReceivedCt1Sampled { .. }
            | State::Ct1Acknowledged { .. }
            | State::Ct2Sampled { .. } => false,
            State::Failed => return None,
        };
        let odd = self.state.epoch() % 2 == 1;
        if sends_header { Some(odd) } else { Some(!odd) }
    }

    /// What the constructors and every transition maintain, stated once so
    /// `from_bytes` can check it last and the tests and fuzz targets can
    /// check it after every step (CR-21).
    ///
    /// The epoch is at least one: `initiator` and `responder` start there
    /// and the two transitions that move it add one. `Failed` carries no
    /// epoch and nothing else, and is a state every honest run can reach, so
    /// it holds trivially. Every variable-length field has the length its
    /// state implies -- `header` is `HEADER_LEN`, `ct1` is `CT1_LEN`,
    /// `ek_vector` is `EK_VECTOR_LEN` -- and every coder is sized for the
    /// value it streams and satisfies its own crate's invariant. A state
    /// failing any of these is one no honest run produced: restoring it
    /// would not panic, since the KEM wrappers length-check, but the next
    /// chunk of its type would end in `Failed` and a forced re-establishment
    /// where `Malformed` was the honest answer, and an oversized encoder
    /// makes the first non-systematic send pay for a quadratic weight
    /// computation over a count the file chose (CR-14, CR-21).
    ///
    /// The key pair the four header-sending states hold passes
    /// [`key_pair_valid`]: the check a completed `ek_vector` passes against
    /// its header, made on the pair's own two public parts. `generate`
    /// produces such a pair and nothing changes one, so every state this
    /// crate builds keeps the clause. A stored pair that breaks it -- a
    /// header hash that is not the hash of the pair's own encapsulation key,
    /// or an `ek_vector` coefficient at or above q -- decapsulates, by
    /// implicit rejection, to a secret the peer does not hold, and the epoch
    /// then ends in `Failed` at the ciphertext MAC rather than at import
    /// (session-persistence.md, register item J-4). The rest of the pair,
    /// its secret half included, has nothing this crate can check it
    /// against, and neither has an `EncapsState`; neither is checked.
    ///
    /// The `ct1` clause is the one `BraidT1`'s `State.ct1_bounded` carries
    /// into `step_receive`, stated exactly rather than as its bound:
    /// `CT1_LEN` is 1408, within the 4096 it asks for.
    ///
    /// Not a clause here, but now a fact of every state this crate builds
    /// or accepts: the epoch is below `u64::MAX`. That value is reserved.
    /// The two transitions that move an epoch refuse the step that would
    /// land on it rather than taking it (transitions (5) and (13)), and
    /// `read_epoch` refuses it on the way in, so what the transitions
    /// produce and what the decoder accepts are the same set of states and
    /// a session this crate exported can always be imported (CR-03).
    ///
    /// It is left out of the clauses below because nothing here needs it:
    /// `read_epoch` has already settled it by the time `from_bytes` runs
    /// this, and the transitions keep it without being asked. Adding
    /// `*epoch < u64::MAX` to the ten arms that carry one would record that
    /// here, but it would still not give the T3 precondition, which asks for
    /// `epoch + 1 < u64::MAX`: the refinement stops one step below the
    /// reservation. `Model.Braid` reserves the same epoch and refuses the
    /// same steps (`Model.Braid.u64Max`), so that premise is kept from
    /// before the model stopped, and whether it could now be dropped has not
    /// been checked. That step is the caller's, and a question for the
    /// proofs rather than for the decoder.
    pub fn invariant(&self) -> bool {
        match &self.state {
            State::KeysUnsampled { epoch, .. } => *epoch >= 1,
            State::KeysSampled {
                epoch, kp, hdr_enc, ..
            } => {
                *epoch >= 1
                    && hdr_enc.invariant()
                    && encoder_sized(hdr_enc, HEADER_LEN + MAC_LEN)
                    && key_pair_valid(kp)
            }
            State::HeaderSent {
                epoch,
                kp,
                ct1_dec,
                ek_enc,
                ..
            } => {
                *epoch >= 1
                    && ct1_dec.invariant()
                    && decoder_sized(ct1_dec, CT1_LEN)
                    && ek_enc.invariant()
                    && encoder_sized(ek_enc, EK_VECTOR_LEN)
                    && key_pair_valid(kp)
            }
            State::Ct1Received {
                epoch,
                kp,
                ct1,
                ek_enc,
                ..
            } => {
                *epoch >= 1
                    && ct1.len() == CT1_LEN
                    && ek_enc.invariant()
                    && encoder_sized(ek_enc, EK_VECTOR_LEN)
                    && key_pair_valid(kp)
            }
            State::EkSentCt1Received {
                epoch,
                kp,
                ct1,
                ct2_dec,
                ..
            } => {
                *epoch >= 1
                    && ct1.len() == CT1_LEN
                    && ct2_dec.invariant()
                    && decoder_sized(ct2_dec, CT2_LEN + MAC_LEN)
                    && key_pair_valid(kp)
            }
            State::NoHeaderReceived { epoch, hdr_dec, .. } => {
                *epoch >= 1 && hdr_dec.invariant() && decoder_sized(hdr_dec, HEADER_LEN + MAC_LEN)
            }
            State::HeaderReceived {
                epoch,
                header,
                ek_dec,
                ..
            } => {
                *epoch >= 1
                    && header.len() == HEADER_LEN
                    && ek_dec.invariant()
                    && decoder_sized(ek_dec, EK_VECTOR_LEN)
            }
            State::Ct1Sampled {
                epoch,
                header,
                ct1,
                ct1_enc,
                ek_dec,
                ..
            } => {
                *epoch >= 1
                    && header.len() == HEADER_LEN
                    && ct1.len() == CT1_LEN
                    && ct1_enc.invariant()
                    && encoder_sized(ct1_enc, CT1_LEN)
                    && ek_dec.invariant()
                    && decoder_sized(ek_dec, EK_VECTOR_LEN)
            }
            State::EkReceivedCt1Sampled {
                epoch,
                ct1,
                ek_vector,
                ct1_enc,
                ..
            } => {
                *epoch >= 1
                    && ct1.len() == CT1_LEN
                    && ek_vector.len() == EK_VECTOR_LEN
                    && ct1_enc.invariant()
                    && encoder_sized(ct1_enc, CT1_LEN)
            }
            State::Ct1Acknowledged {
                epoch,
                header,
                ct1,
                ek_dec,
                ..
            } => {
                *epoch >= 1
                    && header.len() == HEADER_LEN
                    && ct1.len() == CT1_LEN
                    && ek_dec.invariant()
                    && decoder_sized(ek_dec, EK_VECTOR_LEN)
            }
            State::Ct2Sampled { epoch, ct2_enc, .. } => {
                *epoch >= 1 && ct2_enc.invariant() && encoder_sized(ct2_enc, CT2_LEN + MAC_LEN)
            }
            State::Failed => true,
        }
    }

    /// The epoch both parties are known to hold, read after any transition.
    fn reported(&self) -> u64 {
        self.state.epoch().saturating_sub(1)
    }

    /// Produce the next message.
    ///
    /// Returns the message, the epoch both parties are known to hold, and a key
    /// if this send is the moment one became available. Only one state ever
    /// yields a key here: the responder sampling `ct1`, which is the first
    /// moment either party has the epoch's secret.
    /// Takes `&self` and returns the next state rather than advancing in place,
    /// mirroring `receive`.
    ///
    /// A `&mut self` that cannot fail would read as safe and is not once a
    /// caller is composed above it. The session drives this first, because the
    /// Triple Ratchet needs the epoch and output it yields, and the Triple's
    /// own send **can** fail. An in-place advance would mean a failure there
    /// leaves the agreement moved on for a message never sent.
    ///
    /// `Triple::send` follows the same rule one level up, and its doc comment
    /// records why. Returning a candidate makes the caller commit both halves
    /// or neither, which is the only shape that cannot be got wrong by
    /// ordering.
    ///
    /// `#[must_use]`: the tuple carries the only copy of the next state, and a
    /// caller that drops it has sent a message the agreement does not know
    /// about (CR-20).
    #[must_use]
    pub fn send<R: RngCore + CryptoRng>(&self, rng: &mut R) -> (Msg, u64, Option<Output>, Braid) {
        let (msg, out, next) = self.step_send(self.state.clone(), rng);
        let candidate = Braid { state: next };
        (msg, candidate.reported(), out, candidate)
    }

    fn step_send<R: RngCore + CryptoRng>(
        &self,
        state: State,
        rng: &mut R,
    ) -> (Msg, Option<Output>, State) {
        match state {
            // Transition (1): sample a keypair and start sending its header.
            State::KeysUnsampled { epoch, auth } => {
                let kp = match IncrementalKeyPair::generate(rng) {
                    Ok(kp) => kp,
                    Err(_) => return (Msg::empty(epoch), None, State::Failed),
                };
                let header = kp.header();
                let mac = auth.mac_hdr(epoch, &header);
                let mut framed = header;
                framed.extend_from_slice(&mac);
                let mut hdr_enc = Encoder::new(&framed);
                let chunk = hdr_enc.next_chunk();
                (
                    Msg::with(epoch, MsgType::Hdr, chunk),
                    None,
                    State::KeysSampled {
                        epoch,
                        auth,
                        kp,
                        hdr_enc,
                    },
                )
            }
            State::KeysSampled {
                epoch,
                auth,
                kp,
                mut hdr_enc,
            } => {
                let chunk = hdr_enc.next_chunk();
                (
                    Msg::with(epoch, MsgType::Hdr, chunk),
                    None,
                    State::KeysSampled {
                        epoch,
                        auth,
                        kp,
                        hdr_enc,
                    },
                )
            }
            State::HeaderSent {
                epoch,
                auth,
                kp,
                ct1_dec,
                mut ek_enc,
            } => {
                let chunk = ek_enc.next_chunk();
                (
                    Msg::with(epoch, MsgType::Ek, chunk),
                    None,
                    State::HeaderSent {
                        epoch,
                        auth,
                        kp,
                        ct1_dec,
                        ek_enc,
                    },
                )
            }
            State::Ct1Received {
                epoch,
                auth,
                kp,
                ct1,
                mut ek_enc,
            } => {
                let chunk = ek_enc.next_chunk();
                (
                    // The acknowledgement rides on the chunk: this is why the
                    // specification's bare Ct1Ack is never sent.
                    Msg::with(epoch, MsgType::EkCt1Ack, chunk),
                    None,
                    State::Ct1Received {
                        epoch,
                        auth,
                        kp,
                        ct1,
                        ek_enc,
                    },
                )
            }
            State::EkSentCt1Received { epoch, .. } => {
                let s = state_back(state);
                (Msg::empty(epoch), None, s)
            }
            State::NoHeaderReceived { epoch, .. } => {
                let s = state_back(state);
                (Msg::empty(epoch), None, s)
            }
            // Transition (7): sample ct1, and with it the epoch's secret. The
            // responder holds the key from here; the initiator will not until
            // transition (5).
            State::HeaderReceived {
                epoch,
                mut auth,
                header,
                ek_dec,
            } => {
                let (encaps, ct1, mut raw) = match encapsulate1(&header, rng) {
                    Ok(t) => t,
                    Err(_) => return (Msg::empty(epoch), None, State::Failed),
                };
                // The raw shared secret is spent the moment the epoch key is
                // derived from it, and the key lives on only inside `Output`
                // and the authenticator, both of which wipe themselves; the
                // locals here are wiped too, so no copy outlives the step
                // (CR-15).
                let key = Zeroizing::new(kdf_ok(&raw, epoch));
                raw.zeroize();
                auth.update(epoch, &key[..]);
                let mut ct1_enc = Encoder::new(&ct1);
                let chunk = ct1_enc.next_chunk();
                (
                    Msg::with(epoch, MsgType::Ct1, chunk),
                    Some(Output {
                        key_epoch: epoch,
                        key: *key,
                    }),
                    State::Ct1Sampled {
                        epoch,
                        auth,
                        header,
                        encaps,
                        ct1,
                        ct1_enc,
                        ek_dec,
                    },
                )
            }
            State::Ct1Sampled {
                epoch,
                auth,
                header,
                encaps,
                ct1,
                mut ct1_enc,
                ek_dec,
            } => {
                let chunk = ct1_enc.next_chunk();
                (
                    Msg::with(epoch, MsgType::Ct1, chunk),
                    None,
                    State::Ct1Sampled {
                        epoch,
                        auth,
                        header,
                        encaps,
                        ct1,
                        ct1_enc,
                        ek_dec,
                    },
                )
            }
            State::EkReceivedCt1Sampled {
                epoch,
                auth,
                encaps,
                ct1,
                ek_vector,
                mut ct1_enc,
            } => {
                let chunk = ct1_enc.next_chunk();
                (
                    Msg::with(epoch, MsgType::Ct1, chunk),
                    None,
                    State::EkReceivedCt1Sampled {
                        epoch,
                        auth,
                        encaps,
                        ct1,
                        ek_vector,
                        ct1_enc,
                    },
                )
            }
            State::Ct1Acknowledged { epoch, .. } => {
                let s = state_back(state);
                (Msg::empty(epoch), None, s)
            }
            State::Ct2Sampled {
                epoch,
                auth,
                mut ct2_enc,
            } => {
                let chunk = ct2_enc.next_chunk();
                (
                    Msg::with(epoch, MsgType::Ct2, chunk),
                    None,
                    State::Ct2Sampled {
                        epoch,
                        auth,
                        ct2_enc,
                    },
                )
            }
            State::Failed => (Msg::empty(0), None, State::Failed),
        }
    }

    /// Take a message in, **without changing anything**.
    ///
    /// Returns the epoch both parties are known to hold, a key if this message
    /// completed one, and the agreement this message would produce. Only one
    /// state yields a key here: the initiator finishing its decapsulation, which
    /// is the moment both sides hold the epoch's secret.
    ///
    /// Nothing in `self` moves until [`commit`] is called, and the caller must
    /// call it only once the message carrying this one has authenticated.
    ///
    /// [`commit`]: Braid::commit
    ///
    /// ## Why this does not take `&mut self`
    ///
    /// A single received message drives three state machines: this agreement,
    /// the sparse post-quantum ratchet, and the classical one. The other two
    /// advance a candidate and adopt it only on authentication, and a
    /// transaction covering two of three is not a transaction. An in-place
    /// advance here would let a message that never authenticated move the
    /// agreement forward.
    ///
    /// The agreement authenticates its own messages, so the exposure is
    /// narrower than the ratchets'. It would still be the one piece that could
    /// not be rolled back.
    ///
    /// The cost is a copy of the state per received message, which at the
    /// widest is an incremental ML-KEM key pair of nearly twelve kilobytes. The
    /// loser is wiped rather than dropped, because every secret it holds is
    /// behind `Zeroizing`.
    ///
    /// `#[must_use]`: the candidate is the only copy of the state this message
    /// produces; dropping it silently is the same as never having received.
    #[must_use]
    pub fn receive(&self, msg: &Msg) -> (u64, Option<Output>, Braid) {
        let (out, next) = self.step_receive(self.state.clone(), msg);
        let candidate = Braid { state: next };
        match &out {
            // Transition (5) advances the epoch, and the key it emits belongs to
            // the epoch just completed, which is what the advanced state reports.
            Some(o) => (o.key_epoch, out.clone(), candidate),
            None => (candidate.reported(), None, candidate),
        }
    }

    /// Adopt the agreement a [`receive`] produced.
    ///
    /// Call this only after the message that produced it has authenticated.
    ///
    /// [`receive`]: Braid::receive
    pub fn commit(&mut self, next: Braid) {
        *self = next;
    }

    fn step_receive(&self, state: State, msg: &Msg) -> (Option<Output>, State) {
        let epoch = state.epoch();
        let current = msg.epoch == epoch;
        match state {
            State::KeysUnsampled { .. } => (None, state),
            // Transition (2): a ct1 chunk proves the header got through, so stop
            // sending it and start sending ek_vector.
            State::KeysSampled {
                epoch,
                auth,
                kp,
                hdr_enc,
            } => {
                if current && msg.ty == MsgType::Ct1 {
                    if let Some(c) = msg.data {
                        let mut ct1_dec = Decoder::new(CT1_LEN);
                        ct1_dec.add_chunk(c);
                        let ek_enc = Encoder::new(&kp.ek_vector());
                        return (
                            None,
                            State::HeaderSent {
                                epoch,
                                auth,
                                kp,
                                ct1_dec,
                                ek_enc,
                            },
                        );
                    }
                }
                (
                    None,
                    State::KeysSampled {
                        epoch,
                        auth,
                        kp,
                        hdr_enc,
                    },
                )
            }
            // Transition (3): ct1 is complete. It is not authenticated yet; the
            // MAC covering it arrives with ct2.
            State::HeaderSent {
                epoch,
                auth,
                kp,
                mut ct1_dec,
                ek_enc,
            } => {
                if current && msg.ty == MsgType::Ct1 {
                    if let Some(c) = msg.data {
                        ct1_dec.add_chunk(c);
                        if let Some(ct1) = ct1_dec.message() {
                            return (
                                None,
                                State::Ct1Received {
                                    epoch,
                                    auth,
                                    kp,
                                    ct1,
                                    ek_enc,
                                },
                            );
                        }
                    }
                }
                (
                    None,
                    State::HeaderSent {
                        epoch,
                        auth,
                        kp,
                        ct1_dec,
                        ek_enc,
                    },
                )
            }
            // Transition (4): a ct2 chunk proves ek_vector got through.
            State::Ct1Received {
                epoch,
                auth,
                kp,
                ct1,
                ek_enc,
            } => {
                if current && msg.ty == MsgType::Ct2 {
                    if let Some(c) = msg.data {
                        let mut ct2_dec = Decoder::new(CT2_LEN + MAC_LEN);
                        ct2_dec.add_chunk(c);
                        return (
                            None,
                            State::EkSentCt1Received {
                                epoch,
                                auth,
                                kp,
                                ct1,
                                ct2_dec,
                            },
                        );
                    }
                }
                (
                    None,
                    State::Ct1Received {
                        epoch,
                        auth,
                        kp,
                        ct1,
                        ek_enc,
                    },
                )
            }
            // Transition (5): decapsulate, ratchet, verify, emit, advance.
            State::EkSentCt1Received {
                epoch,
                mut auth,
                kp,
                ct1,
                mut ct2_dec,
            } => {
                if current && msg.ty == MsgType::Ct2 {
                    if let Some(c) = msg.data {
                        ct2_dec.add_chunk(c);
                        if let Some(framed) = ct2_dec.message() {
                            if framed.len() != CT2_LEN + MAC_LEN {
                                return (None, State::Failed);
                            }
                            // Checked before anything is derived: an epoch
                            // that cannot be followed cannot complete, and
                            // abandoning the session is the only honest
                            // answer, since nothing this machine could emit
                            // afterwards would carry a number the peer could
                            // agree on.
                            //
                            // `u64::MAX` is reserved, so the step that would
                            // land on it is refused one epoch earlier rather
                            // than taken. Taking it would leave a Braid that
                            // `to_bytes` writes and this crate's own
                            // `from_bytes` then refuses (`read_epoch`) -- a
                            // session exported and unimportable for good,
                            // and one whose next step could only abandon it
                            // anyway. Refused into `Failed` like the arm
                            // above, and for the arm above's reason:
                            // `receive` has no way to say "refused,
                            // unchanged", and a session with no epoch left
                            // to negotiate is what terminal failure is for.
                            // Note what this does and does not leave
                            // usable: this arm both emits the epoch's
                            // output and advances, so refusing here refuses
                            // the *completion* of `u64::MAX - 1`. That
                            // epoch can be entered and held; the last one
                            // both parties agree a key on is
                            // `u64::MAX - 2`. The crate's ceiling test
                            // pins exactly that.
                            // Neither arm is reachable from an honest start
                            // -- epochs begin at one -- so the T1
                            // precondition `epoch < u64::MAX` is now kept by
                            // every transition and not by the decoder alone
                            // (CR-03).
                            let Some(next_epoch) = epoch.checked_add(1) else {
                                return (None, State::Failed);
                            };
                            if next_epoch == u64::MAX {
                                return (None, State::Failed);
                            }
                            let (ct2, mac) = framed.split_at(CT2_LEN);
                            let mut raw = match kp.decapsulate(&ct1, ct2) {
                                Ok(ss) => ss,
                                Err(_) => return (None, State::Failed),
                            };
                            let key = Zeroizing::new(kdf_ok(&raw, epoch));
                            raw.zeroize();
                            // The authenticator ratchets before the MAC is
                            // checked, because the MAC key is what the ratchet
                            // produces. A failure from here is terminal.
                            auth.update(epoch, &key[..]);
                            if !mac_eq(&auth.mac_ct(epoch, &ct1, ct2), mac) {
                                return (None, State::Failed);
                            }
                            return (
                                Some(Output {
                                    key_epoch: epoch,
                                    key: *key,
                                }),
                                State::NoHeaderReceived {
                                    epoch: next_epoch,
                                    auth,
                                    hdr_dec: hdr_decoder(),
                                },
                            );
                        }
                    }
                }
                (
                    None,
                    State::EkSentCt1Received {
                        epoch,
                        auth,
                        kp,
                        ct1,
                        ct2_dec,
                    },
                )
            }
            // Transition (6): the header is complete and its MAC verifies.
            State::NoHeaderReceived {
                epoch,
                auth,
                mut hdr_dec,
            } => {
                if current && msg.ty == MsgType::Hdr {
                    if let Some(c) = msg.data {
                        hdr_dec.add_chunk(c);
                        if let Some(framed) = hdr_dec.message() {
                            if framed.len() != HEADER_LEN + MAC_LEN {
                                return (None, State::Failed);
                            }
                            let (header, mac) = framed.split_at(HEADER_LEN);
                            if !mac_eq(&auth.mac_hdr(epoch, header), mac) {
                                return (None, State::Failed);
                            }
                            return (
                                None,
                                State::HeaderReceived {
                                    epoch,
                                    auth,
                                    header: header.to_vec(),
                                    ek_dec: Decoder::new(EK_VECTOR_LEN),
                                },
                            );
                        }
                    }
                }
                (
                    None,
                    State::NoHeaderReceived {
                        epoch,
                        auth,
                        hdr_dec,
                    },
                )
            }
            // Nothing that matters arrives here. The peer is still in
            // KeysSampled and keeps sending header chunks until a ct1 chunk
            // reaches it, and the ek_vector chunks only start once this party
            // has sent one, which leaves this state; so what arrives is header
            // repeats, and they are ignored.
            State::HeaderReceived { .. } => (None, state),
            // The state with the most ways out: ek_vector completing and the
            // acknowledgement arriving can happen in either order, or together.
            State::Ct1Sampled {
                epoch,
                auth,
                header,
                encaps,
                ct1,
                ct1_enc,
                mut ek_dec,
            } => {
                let relevant = current && (msg.ty == MsgType::Ek || msg.ty == MsgType::EkCt1Ack);
                if relevant {
                    if let Some(c) = msg.data {
                        let acked = msg.ty == MsgType::EkCt1Ack;
                        ek_dec.add_chunk(c);
                        match ek_dec.message() {
                            Some(ek_vector) => {
                                // The only thing between an authenticated header
                                // and a substituted key.
                                if !validate_ek(&header, &ek_vector) {
                                    return (None, State::Failed);
                                }
                                if acked {
                                    // Transition (9): both at once.
                                    return (
                                        None,
                                        finish_encaps(epoch, auth, &encaps, &ct1, &ek_vector),
                                    );
                                }
                                // Transition (10).
                                return (
                                    None,
                                    State::EkReceivedCt1Sampled {
                                        epoch,
                                        auth,
                                        encaps,
                                        ct1,
                                        ek_vector,
                                        ct1_enc,
                                    },
                                );
                            }
                            None => {
                                if acked {
                                    // Transition (8).
                                    return (
                                        None,
                                        State::Ct1Acknowledged {
                                            epoch,
                                            auth,
                                            header,
                                            encaps,
                                            ct1,
                                            ek_dec,
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
                (
                    None,
                    State::Ct1Sampled {
                        epoch,
                        auth,
                        header,
                        encaps,
                        ct1,
                        ct1_enc,
                        ek_dec,
                    },
                )
            }
            // Transition (12).
            State::EkReceivedCt1Sampled {
                epoch,
                auth,
                encaps,
                ct1,
                ek_vector,
                ct1_enc,
            } => {
                if current && msg.ty == MsgType::EkCt1Ack {
                    return (None, finish_encaps(epoch, auth, &encaps, &ct1, &ek_vector));
                }
                (
                    None,
                    State::EkReceivedCt1Sampled {
                        epoch,
                        auth,
                        encaps,
                        ct1,
                        ek_vector,
                        ct1_enc,
                    },
                )
            }
            // Transition (11).
            State::Ct1Acknowledged {
                epoch,
                auth,
                header,
                encaps,
                ct1,
                mut ek_dec,
            } => {
                if current && msg.ty == MsgType::EkCt1Ack {
                    if let Some(c) = msg.data {
                        ek_dec.add_chunk(c);
                        if let Some(ek_vector) = ek_dec.message() {
                            if !validate_ek(&header, &ek_vector) {
                                return (None, State::Failed);
                            }
                            return (None, finish_encaps(epoch, auth, &encaps, &ct1, &ek_vector));
                        }
                    }
                }
                (
                    None,
                    State::Ct1Acknowledged {
                        epoch,
                        auth,
                        header,
                        encaps,
                        ct1,
                        ek_dec,
                    },
                )
            }
            // Transition (13): a message from the next epoch means the peer
            // finished decapsulating. Swap roles.
            State::Ct2Sampled {
                epoch,
                auth,
                ct2_enc,
            } => {
                // Checked for the reason transition (5) gives, and
                // `u64::MAX` is reserved here for the reason it is reserved
                // there: an epoch the session cannot continue from is
                // abandoned, and `Failed` is the only signal `receive` has.
                // Swapping roles onto the ceiling would leave a state this
                // crate exports and then refuses to import, so the step is
                // refused one epoch earlier instead. Neither arm is
                // reachable from an honest start (CR-03).
                let Some(next_epoch) = epoch.checked_add(1) else {
                    return (None, State::Failed);
                };
                if next_epoch == u64::MAX {
                    return (None, State::Failed);
                }
                if msg.epoch == next_epoch {
                    return (
                        None,
                        State::KeysUnsampled {
                            epoch: next_epoch,
                            auth,
                        },
                    );
                }
                (
                    None,
                    State::Ct2Sampled {
                        epoch,
                        auth,
                        ct2_enc,
                    },
                )
            }
            State::Failed => (None, State::Failed),
        }
    }
}

/// Complete the encapsulation and start sending `ct2` with its MAC. Three
/// transitions arrive here, from three different orders of the same two events.
fn finish_encaps(
    epoch: u64,
    auth: Auth,
    encaps: &EncapsState,
    ct1: &[u8],
    ek_vector: &[u8],
) -> State {
    let ct2 = match encapsulate2(encaps, ek_vector) {
        Ok(c) => c,
        Err(_) => return State::Failed,
    };
    let mac = auth.mac_ct(epoch, ct1, &ct2);
    let mut framed = ct2;
    framed.extend_from_slice(&mac);
    State::Ct2Sampled {
        epoch,
        auth,
        ct2_enc: Encoder::new(&framed),
    }
}

/// The states whose `Send` does nothing at all: they return the state they were
/// given. A function rather than a repeated match arm because the borrow checker
/// wants the state moved back out whole.
fn state_back(state: State) -> State {
    state
}

/// The chunk size, re-exported so a caller sizing its envelopes does not have to
/// reach into the codec.
pub const CHUNK_SIZE: usize = CHUNK_BYTES;

/// This crate's own persistence-format version (`Braid::to_bytes`/
/// `from_bytes`), separate from any on-the-wire message version: this is what
/// a storage layer writes to disk and reads back after a restart, not
/// anything a peer ever receives.
const STATE_VERSION: u8 = 0x01;

/// Named with the crate's own prefix rather than plainly `DecodeError`, which
/// reads redundantly inside this crate and is deliberate. Charon emits
/// discriminant instances unqualified, so each crate's error enum carries a
/// distinct name. The redundancy in here buys uniqueness out there. Do not
/// tidy it.
///
/// A `Braid::to_bytes`/`from_bytes` failure. As in the ratchet and the sparse
/// ratchet, this format's threat model is corruption and version skew, not a
/// hostile peer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BraidDecodeError {
    UnknownVersion,
    TooShort,
    Malformed,
}

impl Auth {
    fn to_bytes(&self) -> [u8; 64] {
        let mut out = [0u8; 64];
        out[..32].copy_from_slice(&self.root_key);
        out[32..].copy_from_slice(&self.mac_key);
        out
    }

    fn from_bytes(bytes: &[u8; 64]) -> Auth {
        let mut root_key = [0u8; 32];
        let mut mac_key = [0u8; 32];
        root_key.copy_from_slice(&bytes[..32]);
        mac_key.copy_from_slice(&bytes[32..]);
        Auth { root_key, mac_key }
    }
}

/// The version byte and the state tag, which every persisted state starts
/// with, and the epoch and authenticator every state but `Failed` carries
/// next. Named here so `Braid::encoded_len` states each of them once.
const HEAD_LEN: usize = 1 + 1;
const EPOCH_AND_AUTH_LEN: usize = 8 + 64;

/// What a field of `len` bytes costs in the buffer: its own bytes and the
/// four-byte length `push_len_prefixed` writes ahead of it.
fn len_prefixed_len(len: usize) -> usize {
    4 + len
}

/// Append `bytes` with a four-byte big-endian length ahead of it, so a
/// variable-length field embedded in a larger buffer can be sliced out exactly
/// before its own `from_bytes` sees it -- the sub-formats here (the erasure
/// codec's, the KEM's) each require the exact slice they produced, with no
/// trailing bytes of their own.
fn push_len_prefixed(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
    out.extend_from_slice(bytes);
}

/// Read one length-prefixed field at `pos`, returning it and the position
/// just past it. A plain function, not a loop, so an early return here is
/// unlike the ones this crate's `send`/`receive` avoid inside loops.
fn take_len_prefixed(bytes: &[u8], pos: usize) -> Option<(&[u8], usize)> {
    // `checked_add` on both sums. On a 32-bit target a length near
    // `u32::MAX` would make `start + len` wrap to a small value, pass the
    // bounds check, and panic on the slice -- the unchecked-slice class the
    // wire decoders' `take_at` guards against. Written as matches rather than
    // `?` to stay in the translatable subset.
    let start = match pos.checked_add(4) {
        Some(s) => s,
        None => return None,
    };
    if bytes.len() < start {
        return None;
    }
    let mut len_bytes = [0u8; 4];
    len_bytes.copy_from_slice(&bytes[pos..start]);
    let len = u32::from_be_bytes(len_bytes) as usize;
    let end = match start.checked_add(len) {
        Some(e) => e,
        None => return None,
    };
    if bytes.len() < end {
        return None;
    }
    Some((&bytes[start..end], end))
}

fn read_u64(bytes: &[u8], pos: usize) -> Option<u64> {
    if bytes.len() < pos + 8 {
        return None;
    }
    let mut b = [0u8; 8];
    b.copy_from_slice(&bytes[pos..pos + 8]);
    Some(u64::from_be_bytes(b))
}

/// Read a persisted epoch, refusing `u64::MAX`.
///
/// The value is reserved and no run reaches it: epochs start at one, and the
/// two transitions that move one refuse the step that would land on it
/// rather than taking it (transitions (5) and (13)). So this refuses a state
/// the operations cannot produce -- corruption, or a store written to by
/// something else -- and refuses nothing this crate can export. That
/// agreement between the decoder and the transitions is the point of the
/// reservation: it is what makes the T1 theorem's precondition
/// `epoch < u64::MAX` a property of every state a run can reach, rather than
/// a policy the decoder imposes on the top of the range (CR-03).
fn read_epoch(bytes: &[u8], pos: usize) -> Option<u64> {
    let Some(e) = read_u64(bytes, pos) else {
        return None;
    };
    if e == u64::MAX {
        return None;
    }
    Some(e)
}

fn read_auth(bytes: &[u8], pos: usize) -> Option<(Auth, usize)> {
    if bytes.len() < pos + 64 {
        return None;
    }
    let mut a = [0u8; 64];
    a.copy_from_slice(&bytes[pos..pos + 64]);
    Some((Auth::from_bytes(&a), pos + 64))
}

impl Braid {
    /// Encode this agreement for persistence. Not a message on the wire --
    /// see the ratchet and session layers for that -- this is what a storage
    /// layer writes to disk and reads back with `from_bytes` after a
    /// restart. Every state carries `Auth`'s two keys and several carry an
    /// `IncrementalKeyPair` up to nearly twelve kilobytes, so this can be a
    /// large buffer; at-rest protection of it is the caller's job, the same
    /// as for the ratchet and sparse-ratchet formats.
    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        // Wrapped, as the other three ratchet-layer `to_bytes` are, and as the
        // erasure crate's comment on its own unwrapped `to_bytes` says this one
        // is: the buffer carries the authenticator's root and MAC keys and, in
        // five of the states, the whole decapsulation key.
        let len = self.encoded_len();
        let mut out = Vec::with_capacity(len);
        out.push(STATE_VERSION);
        out.push(self.state_tag());
        match &self.state {
            State::KeysUnsampled { epoch, auth } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
            }
            State::KeysSampled {
                epoch,
                auth,
                kp,
                hdr_enc,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, &kp.to_bytes());
                push_len_prefixed(&mut out, &hdr_enc.to_bytes());
            }
            State::HeaderSent {
                epoch,
                auth,
                kp,
                ct1_dec,
                ek_enc,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, &kp.to_bytes());
                push_len_prefixed(&mut out, &ct1_dec.to_bytes());
                push_len_prefixed(&mut out, &ek_enc.to_bytes());
            }
            State::Ct1Received {
                epoch,
                auth,
                kp,
                ct1,
                ek_enc,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, &kp.to_bytes());
                push_len_prefixed(&mut out, ct1);
                push_len_prefixed(&mut out, &ek_enc.to_bytes());
            }
            State::EkSentCt1Received {
                epoch,
                auth,
                kp,
                ct1,
                ct2_dec,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, &kp.to_bytes());
                push_len_prefixed(&mut out, ct1);
                push_len_prefixed(&mut out, &ct2_dec.to_bytes());
            }
            State::NoHeaderReceived {
                epoch,
                auth,
                hdr_dec,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, &hdr_dec.to_bytes());
            }
            State::HeaderReceived {
                epoch,
                auth,
                header,
                ek_dec,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, header);
                push_len_prefixed(&mut out, &ek_dec.to_bytes());
            }
            State::Ct1Sampled {
                epoch,
                auth,
                header,
                encaps,
                ct1,
                ct1_enc,
                ek_dec,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, header);
                push_len_prefixed(&mut out, &encaps.to_bytes());
                push_len_prefixed(&mut out, ct1);
                push_len_prefixed(&mut out, &ct1_enc.to_bytes());
                push_len_prefixed(&mut out, &ek_dec.to_bytes());
            }
            State::EkReceivedCt1Sampled {
                epoch,
                auth,
                encaps,
                ct1,
                ek_vector,
                ct1_enc,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, &encaps.to_bytes());
                push_len_prefixed(&mut out, ct1);
                push_len_prefixed(&mut out, ek_vector);
                push_len_prefixed(&mut out, &ct1_enc.to_bytes());
            }
            State::Ct1Acknowledged {
                epoch,
                auth,
                header,
                encaps,
                ct1,
                ek_dec,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, header);
                push_len_prefixed(&mut out, &encaps.to_bytes());
                push_len_prefixed(&mut out, ct1);
                push_len_prefixed(&mut out, &ek_dec.to_bytes());
            }
            State::Ct2Sampled {
                epoch,
                auth,
                ct2_enc,
            } => {
                out.extend_from_slice(&epoch.to_be_bytes());
                out.extend_from_slice(&auth.to_bytes());
                push_len_prefixed(&mut out, &ct2_enc.to_bytes());
            }
            State::Failed => {}
        }
        // The buffer is the length `encoded_len` said it would be, so it was
        // never grown. A `Vec` that grows moves what it holds -- here the
        // authenticator's root and MAC keys and, in five of these states, the
        // whole decapsulation key -- into a larger allocation and hands the
        // smaller one back to the allocator unwiped, where the `Zeroizing`
        // wrapper below no longer reaches it. The assertion is what keeps the
        // formula and the writes from drifting apart.
        debug_assert_eq!(out.len(), len);
        Zeroizing::new(out)
    }

    /// Exactly how many bytes `to_bytes` writes for this state: the version
    /// byte and the tag, then, in every state but `Failed`, the epoch and the
    /// authenticator, then each variable-length field with the four-byte
    /// length `push_len_prefixed` writes ahead of it.
    ///
    /// The lengths of the two `tacenta-kem` values are fixed for a build but
    /// that crate does not export them, so measuring one means asking it for
    /// its bytes. The buffer that costs is exactly sized and wiped when it
    /// drops, which is precisely what growing the output buffer instead would
    /// not be; exporting the two lengths from `tacenta-kem` would remove the
    /// copy and leave this pure arithmetic.
    fn encoded_len(&self) -> usize {
        match &self.state {
            State::KeysUnsampled { .. } => HEAD_LEN + EPOCH_AND_AUTH_LEN,
            State::KeysSampled { kp, hdr_enc, .. } => {
                HEAD_LEN
                    + EPOCH_AND_AUTH_LEN
                    + len_prefixed_len(kp.to_bytes().len())
                    + len_prefixed_len(hdr_enc.encoded_len())
            }
            State::HeaderSent {
                kp,
                ct1_dec,
                ek_enc,
                ..
            } => {
                HEAD_LEN
                    + EPOCH_AND_AUTH_LEN
                    + len_prefixed_len(kp.to_bytes().len())
                    + len_prefixed_len(ct1_dec.encoded_len())
                    + len_prefixed_len(ek_enc.encoded_len())
            }
            State::Ct1Received {
                kp, ct1, ek_enc, ..
            } => {
                HEAD_LEN
                    + EPOCH_AND_AUTH_LEN
                    + len_prefixed_len(kp.to_bytes().len())
                    + len_prefixed_len(ct1.len())
                    + len_prefixed_len(ek_enc.encoded_len())
            }
            State::EkSentCt1Received {
                kp, ct1, ct2_dec, ..
            } => {
                HEAD_LEN
                    + EPOCH_AND_AUTH_LEN
                    + len_prefixed_len(kp.to_bytes().len())
                    + len_prefixed_len(ct1.len())
                    + len_prefixed_len(ct2_dec.encoded_len())
            }
            State::NoHeaderReceived { hdr_dec, .. } => {
                HEAD_LEN + EPOCH_AND_AUTH_LEN + len_prefixed_len(hdr_dec.encoded_len())
            }
            State::HeaderReceived { header, ek_dec, .. } => {
                HEAD_LEN
                    + EPOCH_AND_AUTH_LEN
                    + len_prefixed_len(header.len())
                    + len_prefixed_len(ek_dec.encoded_len())
            }
            State::Ct1Sampled {
                header,
                encaps,
                ct1,
                ct1_enc,
                ek_dec,
                ..
            } => {
                HEAD_LEN
                    + EPOCH_AND_AUTH_LEN
                    + len_prefixed_len(header.len())
                    + len_prefixed_len(encaps.to_bytes().len())
                    + len_prefixed_len(ct1.len())
                    + len_prefixed_len(ct1_enc.encoded_len())
                    + len_prefixed_len(ek_dec.encoded_len())
            }
            State::EkReceivedCt1Sampled {
                encaps,
                ct1,
                ek_vector,
                ct1_enc,
                ..
            } => {
                HEAD_LEN
                    + EPOCH_AND_AUTH_LEN
                    + len_prefixed_len(encaps.to_bytes().len())
                    + len_prefixed_len(ct1.len())
                    + len_prefixed_len(ek_vector.len())
                    + len_prefixed_len(ct1_enc.encoded_len())
            }
            State::Ct1Acknowledged {
                header,
                encaps,
                ct1,
                ek_dec,
                ..
            } => {
                HEAD_LEN
                    + EPOCH_AND_AUTH_LEN
                    + len_prefixed_len(header.len())
                    + len_prefixed_len(encaps.to_bytes().len())
                    + len_prefixed_len(ct1.len())
                    + len_prefixed_len(ek_dec.encoded_len())
            }
            State::Ct2Sampled { ct2_enc, .. } => {
                HEAD_LEN + EPOCH_AND_AUTH_LEN + len_prefixed_len(ct2_enc.encoded_len())
            }
            State::Failed => HEAD_LEN,
        }
    }

    /// Decode a `Braid` persisted by `to_bytes`.
    pub fn from_bytes(bytes: &[u8]) -> Result<Braid, BraidDecodeError> {
        if bytes.len() < 2 {
            return Err(BraidDecodeError::TooShort);
        }
        if bytes[0] != STATE_VERSION {
            return Err(BraidDecodeError::UnknownVersion);
        }
        let tag = bytes[1];
        let state = match decode_state(tag, bytes, 2) {
            Some((state, pos)) if pos == bytes.len() => state,
            Some(_) => return Err(BraidDecodeError::Malformed),
            None => return Err(BraidDecodeError::Malformed),
        };
        // Framed and parsed is not the same as reachable: the lengths and
        // coder sizes every state implies are `invariant`'s, checked last
        // as one predicate so what the decoder accepts and what the
        // transitions keep are the same statement (CR-21).
        let braid = Braid { state };
        if !braid.invariant() {
            return Err(BraidDecodeError::Malformed);
        }
        Ok(braid)
    }
}

/// Whether an encoder is sized for a value of `len` bytes, and a decoder is
/// expecting exactly `len` bytes. Every coder a state carries is built for
/// one fixed length, so a coder of any other size is one no honest run
/// produced; `Braid::invariant` says what admitting one would cost.
fn encoder_sized(enc: &Encoder, len: usize) -> bool {
    enc.needed() == chunk_count(len)
}

fn decoder_sized(dec: &Decoder, len: usize) -> bool {
    dec.size() == len
}

/// Whether a stored key pair's own header and encapsulation-key vector pass
/// the check a completed `ek_vector` passes against a received header: the
/// header's `H(ek)` is the hash of `ek_vector || rho`, which is FIPS 203
/// section 7.3's hash check made on the incremental key pair, whose
/// decapsulation uses that hash; and every coefficient of `ek_vector` is
/// below q, section 7.2's modulus check (session-persistence.md, Braid).
///
/// `validate_ek` belongs to the trusted boundary (`tacenta-kem`, over
/// libcrux's `validate_pk_bytes`), and reaches the translation as the same
/// opaque declaration `step_receive` already calls, as do `header` and
/// `ek_vector`, so this check adds no declaration to it. What it covers is
/// the pair's public half and nothing more; `Braid::invariant` says what is
/// left.
fn key_pair_valid(kp: &IncrementalKeyPair) -> bool {
    let header = kp.header();
    let ek_vector = kp.ek_vector();
    validate_ek(&header, &ek_vector)
}

/// Decode one state variant's fields (everything after the tag byte),
/// returning it and the position just past its last field. A plain function
/// with early returns throughout: nothing here loops.
///
/// Framing only. Whether every variable-length field has the length its
/// state implies and every coder is sized for the value it streams is
/// `Braid::invariant`'s question, which `from_bytes` asks once this returns,
/// so that what comes back is a state some honest run could have been in
/// (CR-21).
fn decode_state(tag: u8, bytes: &[u8], pos: usize) -> Option<(State, usize)> {
    match tag {
        0 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            Some((State::KeysUnsampled { epoch, auth }, pos))
        }
        1 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((kp_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Ok(kp) = IncrementalKeyPair::from_bytes(kp_bytes) else {
                return None;
            };
            let Some((hdr_enc_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(hdr_enc) = Encoder::from_bytes(hdr_enc_bytes) else {
                return None;
            };
            Some((
                State::KeysSampled {
                    epoch,
                    auth,
                    kp,
                    hdr_enc,
                },
                pos,
            ))
        }
        2 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((kp_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Ok(kp) = IncrementalKeyPair::from_bytes(kp_bytes) else {
                return None;
            };
            let Some((ct1_dec_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ct1_dec) = Decoder::from_bytes(ct1_dec_bytes) else {
                return None;
            };
            let Some((ek_enc_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ek_enc) = Encoder::from_bytes(ek_enc_bytes) else {
                return None;
            };
            Some((
                State::HeaderSent {
                    epoch,
                    auth,
                    kp,
                    ct1_dec,
                    ek_enc,
                },
                pos,
            ))
        }
        3 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((kp_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Ok(kp) = IncrementalKeyPair::from_bytes(kp_bytes) else {
                return None;
            };
            let Some((ct1, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some((ek_enc_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ek_enc) = Encoder::from_bytes(ek_enc_bytes) else {
                return None;
            };
            Some((
                State::Ct1Received {
                    epoch,
                    auth,
                    kp,
                    ct1: ct1.to_vec(),
                    ek_enc,
                },
                pos,
            ))
        }
        4 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((kp_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Ok(kp) = IncrementalKeyPair::from_bytes(kp_bytes) else {
                return None;
            };
            let Some((ct1, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some((ct2_dec_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ct2_dec) = Decoder::from_bytes(ct2_dec_bytes) else {
                return None;
            };
            Some((
                State::EkSentCt1Received {
                    epoch,
                    auth,
                    kp,
                    ct1: ct1.to_vec(),
                    ct2_dec,
                },
                pos,
            ))
        }
        5 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((hdr_dec_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(hdr_dec) = Decoder::from_bytes(hdr_dec_bytes) else {
                return None;
            };
            Some((
                State::NoHeaderReceived {
                    epoch,
                    auth,
                    hdr_dec,
                },
                pos,
            ))
        }
        6 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((header, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some((ek_dec_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ek_dec) = Decoder::from_bytes(ek_dec_bytes) else {
                return None;
            };
            Some((
                State::HeaderReceived {
                    epoch,
                    auth,
                    header: header.to_vec(),
                    ek_dec,
                },
                pos,
            ))
        }
        7 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((header, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some((encaps_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Ok(encaps) = EncapsState::from_bytes(encaps_bytes) else {
                return None;
            };
            let Some((ct1, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some((ct1_enc_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ct1_enc) = Encoder::from_bytes(ct1_enc_bytes) else {
                return None;
            };
            let Some((ek_dec_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ek_dec) = Decoder::from_bytes(ek_dec_bytes) else {
                return None;
            };
            Some((
                State::Ct1Sampled {
                    epoch,
                    auth,
                    header: header.to_vec(),
                    encaps,
                    ct1: ct1.to_vec(),
                    ct1_enc,
                    ek_dec,
                },
                pos,
            ))
        }
        8 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((encaps_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Ok(encaps) = EncapsState::from_bytes(encaps_bytes) else {
                return None;
            };
            let Some((ct1, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some((ek_vector, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some((ct1_enc_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ct1_enc) = Encoder::from_bytes(ct1_enc_bytes) else {
                return None;
            };
            Some((
                State::EkReceivedCt1Sampled {
                    epoch,
                    auth,
                    encaps,
                    ct1: ct1.to_vec(),
                    ek_vector: ek_vector.to_vec(),
                    ct1_enc,
                },
                pos,
            ))
        }
        9 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((header, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some((encaps_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Ok(encaps) = EncapsState::from_bytes(encaps_bytes) else {
                return None;
            };
            let Some((ct1, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some((ek_dec_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ek_dec) = Decoder::from_bytes(ek_dec_bytes) else {
                return None;
            };
            Some((
                State::Ct1Acknowledged {
                    epoch,
                    auth,
                    header: header.to_vec(),
                    encaps,
                    ct1: ct1.to_vec(),
                    ek_dec,
                },
                pos,
            ))
        }
        10 => {
            let Some(epoch) = read_epoch(bytes, pos) else {
                return None;
            };
            let Some((auth, pos)) = read_auth(bytes, pos + 8) else {
                return None;
            };
            let Some((ct2_enc_bytes, pos)) = take_len_prefixed(bytes, pos) else {
                return None;
            };
            let Some(ct2_enc) = Encoder::from_bytes(ct2_enc_bytes) else {
                return None;
            };
            Some((
                State::Ct2Sampled {
                    epoch,
                    auth,
                    ct2_enc,
                },
                pos,
            ))
        }
        11 => Some((State::Failed, pos)),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
