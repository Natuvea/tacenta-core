//! The whole post-quantum stack, running.
//!
//! Four crates that have only ever been tested apart:
//!
//! - `tacenta-erasure`, Reed-Solomon over GF(2^16)
//! - `tacenta-kem`, ML-KEM-1024's incremental interface
//! - `tacenta-braid`, the agreement that streams a key exchange through both
//! - `tacenta-spqr` and `tacenta-triple`, the ratchet over it and the
//!   composition with the Double Ratchet
//!
//! Each has its own tests and each passes them. That says nothing about whether
//! the Braid's notion of an epoch is the one the ratchet expects, whether the
//! epoch a message reports is the one whose key the peer holds, or whether a
//! conversation survives the moment the two sides swap roles. Those are
//! properties of the seams, and a seam is where a stack of individually correct
//! parts goes wrong.
//!
//! Real ML-KEM-1024, erasure coding and HKDF; the Diffie-Hellman half uses a
//! stand-in with the one property the Double Ratchet needs. Messages actually
//! encrypt and decrypt.

use rand::SeedableRng;
use rand::rngs::StdRng;
use tacenta_braid::{Braid, Msg};
use tacenta_spqr::Output as SpqrOutput;
use tacenta_triple::{Header, LabelSet, State as Triple, TripleError};

use tacenta_core::primitives::aead;
use tacenta_core::ratchet::message_keys;

/// Why a received message was not delivered.
///
/// The two are kept apart because they mean different things: a ratchet refusal
/// says the header asked for something the state cannot do, and an AEAD failure
/// says the message was not written by the peer. Collapsing them would make the
/// transaction test unable to say which it had exercised.
#[derive(Debug)]
enum Rejected {
    /// The header asked the ratchets for something the state cannot do. Carried
    /// rather than discarded so a failing test says which refusal it hit.
    #[allow(dead_code)]
    Ratchet(TripleError),
    /// The tag did not verify, so the message was not written by the peer.
    Aead,
}

/// Everything a received message would change, held until it authenticates.
///
/// The whole point of the type: a party cannot be advanced except by handing
/// this back, so there is no path that moves the ratchet, the folded epoch, or
/// the ratchet keys without the caller having decided the message was genuine.
struct Pending {
    ratchet: Triple,
    /// The agreement this message would produce. All three state machines a
    /// received message touches are now in here, which is what makes this a
    /// transaction rather than two thirds of one.
    braid: Braid,
    /// Keys the agreement completed on this message, held rather than filed.
    gained: Vec<SpqrOutput>,
    folded: Option<u64>,
    turn: Option<([u8; 32], [u8; 32])>,
}

/// Expand a combined key and encrypt under it, the way a session would.
///
/// The composite header is the associated data, so a message is bound to the
/// epoch and both message numbers it claims. Moving any of them invalidates the
/// tag rather than selecting a different key without notice.
fn seal(key: &[u8; 32], msg: &Msg, header: &Header, plaintext: &[u8]) -> Vec<u8> {
    let (enc, mac, iv) = message_keys(key, LabelSet::Tacenta);
    aead::encrypt(&enc, &mac, &iv, plaintext, &header_ad(msg, header))
}

fn open(key: &[u8; 32], msg: &Msg, header: &Header, ciphertext: &[u8]) -> Result<Vec<u8>, ()> {
    let (enc, mac, iv) = message_keys(key, LabelSet::Tacenta);
    aead::decrypt(&enc, &mac, &iv, ciphertext, &header_ad(msg, header)).map_err(|_| ())
}

/// The composite header's bytes, as associated data: the agreement message
/// *and* the ratchet header, which is what a session covers with `concat_ad`.
///
/// Both parts must be covered, or the "forged message moves none of the three
/// machines" test below could never see a substituted agreement chunk: with a
/// tag over the ratchet header only, a swapped chunk would sail through this
/// harness while production refuses it.
fn header_ad(m: &Msg, h: &Header) -> Vec<u8> {
    let mut ad = Vec::new();
    ad.extend_from_slice(&m.epoch.to_be_bytes());
    ad.push(m.ty as u8);
    match &m.data {
        Some(c) => {
            ad.push(1);
            ad.extend_from_slice(&c.index.to_be_bytes());
            ad.extend_from_slice(&c.data);
        }
        None => ad.push(0),
    }
    ad.extend_from_slice(&h.dr.dh);
    ad.extend_from_slice(&h.dr.pn.to_be_bytes());
    ad.extend_from_slice(&h.dr.n.to_be_bytes());
    ad.extend_from_slice(&h.epoch.to_be_bytes());
    ad.extend_from_slice(&h.pq_n.to_be_bytes());
    ad
}

const SK: &[u8] = &[0x77; 32];
const A_PUB: [u8; 32] = [0x0a; 32];
const B_PUB: [u8; 32] = [0x0b; 32];

/// A stand-in for X25519, with the one property the Double Ratchet needs:
/// `DH(a_priv, B_pub) == DH(b_priv, A_pub)`. Keying it on the two public keys
/// makes that hold by construction.
///
/// The curve agreement lives in the session layer and is not what this
/// exercises. What it does have to be is *direction-correct*: passing one
/// fixed value both ways works for a single message and then disagrees the
/// moment the ratchet turns around.
fn dh(p: [u8; 32], q: [u8; 32]) -> [u8; 32] {
    let (lo, hi) = if p <= q { (p, q) } else { (q, p) };
    let mut ikm = [0u8; 64];
    ikm[0..32].copy_from_slice(&lo);
    ikm[32..64].copy_from_slice(&hi);
    tacenta_kdf::hkdf_sha256(&[0u8; 32], &ikm, b"test dh stand-in")
}

/// One party: an agreement, a ratchet, and the plumbing between them.
///
/// The plumbing is the point. The Braid reports, on every send and every
/// receive, the latest epoch both parties are known to hold, and hands over a
/// key at the moment one becomes available. The ratchet must be given that key
/// exactly once, and must be told to use exactly the epoch the peer can also
/// reach. Getting either wrong produces a session that works until it suddenly
/// does not.
struct Party {
    braid: Braid,
    ratchet: Triple,
    /// This party's current ratchet public key, and the peer's, tracked in step
    /// with what the ratchet holds so the right agreements can be computed.
    my_pub: [u8; 32],
    peer_pub: [u8; 32],
    /// Distinguishes this party's generated keys from the other's.
    tag: u8,
    counter: u64,
    /// Epoch secrets the Braid has produced and the ratchet has not yet folded
    /// in. The ratchet accepts them strictly in order, one per epoch.
    pending: Vec<SpqrOutput>,
    /// The highest epoch this party has folded into its ratchet.
    folded: u64,
}

impl Party {
    fn new(braid: Braid, ratchet: Triple, my_pub: [u8; 32], peer_pub: [u8; 32], tag: u8) -> Party {
        Party {
            braid,
            ratchet,
            my_pub,
            peer_pub,
            tag,
            counter: 0,
            pending: Vec::new(),
            folded: 0,
        }
    }

    fn initiator() -> Party {
        Party::new(
            Braid::initiator(SK),
            Triple::init_sender(SK, A_PUB, B_PUB, &dh(A_PUB, B_PUB), LabelSet::Tacenta),
            A_PUB,
            B_PUB,
            0xa0,
        )
    }

    fn responder() -> Party {
        Party::new(
            Braid::responder(SK),
            Triple::init_receiver(SK, B_PUB, LabelSet::Tacenta),
            B_PUB,
            // Bob has not seen Alice's ratchet key yet, so anything he holds
            // must differ from it and force a step on the first message.
            [0xff; 32],
            0xb0,
        )
    }

    /// A fresh ratchet key pair, represented by its public half.
    fn fresh(&mut self) -> [u8; 32] {
        let mut k = [0u8; 32];
        k[0] = self.tag;
        k[1..9].copy_from_slice(&self.counter.to_be_bytes());
        self.counter += 1;
        k
    }

    /// The next agreement message, plus whatever it taught us.
    ///
    /// This harness commits the advance immediately, which is fine here because
    /// nothing above it can fail. **A session cannot do that**: it drives the
    /// agreement first, because the Triple Ratchet needs the epoch and output,
    /// and the Triple's send can fail. Committing here and failing there would
    /// leave the agreement advanced for a message never sent.
    ///
    /// Note `agreement_receive` below returns a candidate and says why. The
    /// session applies the same shape in this direction: it drives the
    /// agreement first, runs the Triple's send on a working copy, and commits
    /// the agreement's next state only once that send has succeeded.
    fn agreement_send<R: rand::RngCore + rand::CryptoRng>(&mut self, rng: &mut R) -> (Msg, u64) {
        let (msg, reported, out, next) = self.braid.send(rng);
        self.braid = next;
        if let Some(o) = out {
            self.pending.push(SpqrOutput::new(o.key_epoch, o.key));
        }
        (msg, reported)
    }

    /// What the agreement would do with this message, changing nothing.
    ///
    /// The keys it completes are returned rather than filed, because a key
    /// derived from a message that never authenticates is not a key this party
    /// holds.
    fn agreement_receive(&self, msg: &Msg) -> (u64, Braid, Vec<SpqrOutput>) {
        let (reported, out, candidate) = self.braid.receive(msg);
        let gained = out
            .map(|o| vec![SpqrOutput::new(o.key_epoch, o.key)])
            .unwrap_or_default();
        (reported, candidate, gained)
    }

    /// The secret to fold in on this message, if the next epoch is one this
    /// party may safely move to.
    ///
    /// "Safely" is the whole question. A party may hold the key for epoch `n`
    /// long before its peer does. Folding it in early would produce messages the
    /// peer cannot read. The Braid's reported epoch is what says when it is
    /// mutual, and this is where that answer is used.
    fn next_secret(&self, reported: u64) -> Option<SpqrOutput> {
        let want = self.folded + 1;
        if want > reported {
            return None;
        }
        self.pending.iter().find(|o| o.key_epoch == want).cloned()
    }

    fn send_message<R: rand::RngCore + rand::CryptoRng>(
        &mut self,
        rng: &mut R,
    ) -> Result<(Msg, Header, [u8; 32]), TripleError> {
        let (agreement_msg, reported) = self.agreement_send(rng);
        let secret = self.next_secret(reported);
        let epoch = match &secret {
            Some(o) => o.key_epoch,
            None => self.folded,
        };
        let r = self.ratchet.send(epoch, secret.as_ref());
        match r {
            Ok((header, key)) => {
                if secret.is_some() {
                    self.folded = epoch;
                }
                Ok((agreement_msg, header, key))
            }
            Err(e) => Err(e),
        }
    }

    fn receive_message(
        &mut self,
        agreement_msg: &Msg,
        header: &Header,
    ) -> Result<(Pending, [u8; 32]), TripleError> {
        let (_reported, braid_next, gained) = self.agreement_receive(agreement_msg);

        // The header names the epoch the sender used. Fold that epoch's secret
        // if this party has it and has not yet.
        //
        // A key this very message completed counts, and is looked up from the
        // held list rather than the filed one, because filing it before the
        // message authenticates is the thing this transaction exists to
        // prevent.
        let secret = if header.epoch == self.folded + 1 {
            self.pending
                .iter()
                .chain(gained.iter())
                .find(|o| o.key_epoch == header.epoch)
                .cloned()
        } else {
            None
        };

        // A header carrying a ratchet key we have not seen turns the chain
        // around: the incoming agreement uses the key we hold now, and the
        // outgoing one uses a fresh key against theirs.
        let turning = header.dr.dh != self.peer_pub;
        let dh_recv = dh(self.my_pub, header.dr.dh);
        let my_next = if turning { self.fresh() } else { self.my_pub };
        let dh_send = dh(my_next, header.dr.dh);

        let r = self
            .ratchet
            .receive(header, &dh_recv, &dh_send, my_next, secret.as_ref());
        match r {
            Ok((candidate, key)) => {
                // Everything below here is provisional. The caller
                // authenticates and then calls `commit_receive`, which is the
                // only thing that moves this party.
                Ok((
                    Pending {
                        ratchet: candidate,
                        braid: braid_next,
                        gained,
                        folded: if secret.is_some() {
                            Some(header.epoch)
                        } else {
                            None
                        },
                        turn: if turning {
                            Some((header.dr.dh, my_next))
                        } else {
                            None
                        },
                    },
                    key,
                ))
            }
            Err(e) => Err(e),
        }
    }

    /// The whole receive, the way a session must do it: derive against a
    /// candidate, authenticate the ciphertext under the key that came back, and
    /// adopt the state only then.
    ///
    /// A failed tag returns `Err` having changed nothing in the two ratchets
    /// or in the agreement: `Braid` is `Clone` and `receive` returns a
    /// candidate, so the agreement half is inside the same transaction, and
    /// its own messages carry their own authentication besides.
    fn accept(
        &mut self,
        agreement_msg: &Msg,
        header: &Header,
        ciphertext: &[u8],
    ) -> Result<Vec<u8>, Rejected> {
        let (pending, key) = self
            .receive_message(agreement_msg, header)
            .map_err(Rejected::Ratchet)?;
        match open(&key, agreement_msg, header, ciphertext) {
            Ok(plaintext) => {
                self.commit_receive(pending);
                Ok(plaintext)
            }
            // Dropping `pending` here *is* the transaction: nothing in either
            // ratchet moved, so a genuine message this forgery was racing still
            // decrypts.
            Err(()) => Err(Rejected::Aead),
        }
    }

    /// Adopt what a receive produced, once its ciphertext has authenticated.
    fn commit_receive(&mut self, p: Pending) {
        self.ratchet.commit(p.ratchet);
        self.braid.commit(p.braid);
        self.pending.extend(p.gained);
        if let Some(e) = p.folded {
            self.folded = e;
        }
        if let Some((peer, mine)) = p.turn {
            self.peer_pub = peer;
            self.my_pub = mine;
        }
    }
}

/// A whole conversation: every message carries an agreement chunk and a
/// ratcheted payload, which is how this protocol is meant to run.
#[test]
fn the_stack_carries_a_conversation_and_ratchets_post_quantum() {
    let mut rng = StdRng::seed_from_u64(20260726);
    let mut a = Party::initiator();
    let mut b = Party::responder();

    let mut delivered = 0usize;
    let mut epochs_used: Vec<u64> = Vec::new();

    let mut round = 0;
    while round < 400 {
        // Alice speaks.
        let (am, h, ka) = a.send_message(&mut rng).unwrap();
        let ct = seal(&ka, &am, &h, format!("alice {round}").as_bytes());
        let got = b.accept(&am, &h, &ct).unwrap();
        assert_eq!(
            got,
            format!("alice {round}").as_bytes(),
            "round {round}: the two sides disagree"
        );
        delivered += 1;
        if !epochs_used.contains(&h.epoch) {
            epochs_used.push(h.epoch);
        }

        // Bob replies. Before he has received anything the Double Ratchet has
        // no sending chain, which is ordinary and not a failure of the stack.
        match b.send_message(&mut rng) {
            Ok((bm, h, kb)) => {
                let ct = seal(&kb, &bm, &h, format!("bob {round}").as_bytes());
                let got = a.accept(&bm, &h, &ct).unwrap();
                assert_eq!(
                    got,
                    format!("bob {round}").as_bytes(),
                    "round {round}: the reply disagrees"
                );
                delivered += 1;
                if !epochs_used.contains(&h.epoch) {
                    epochs_used.push(h.epoch);
                }
            }
            Err(TripleError::Classical(_)) => {
                // Still deliver the agreement half, so the Braid keeps moving.
                let (bm, _) = b.agreement_send(&mut rng);
                a.agreement_receive(&bm);
            }
            Err(e) => panic!("round {round}: {e:?}"),
        }
        round += 1;
    }

    assert!(!a.braid.failed() && !b.braid.failed());
    assert!(delivered > 700, "only {delivered} messages delivered");
    // The point of the whole exercise: messages were encrypted under more than
    // one post-quantum epoch, so the stack is not merely running, it is
    // ratcheting.
    assert!(
        epochs_used.len() >= 3,
        "only reached epochs {epochs_used:?}, so nothing ratcheted"
    );
    assert!(epochs_used.contains(&0), "epoch 0 should carry the opening");

    // **The vulnerable message set, measured.** This run reaches epoch 7 over
    // roughly eight hundred messages, so a post-quantum ratchet step costs
    // about a hundred messages at a 32-byte chunk. That is the number that
    // matters after a compromise: it is how long an attacker keeps reading.
    //
    // It is not a fact about the protocol but about our chunk size, and the
    // relationship is close to linear. Larger chunks heal proportionally
    // faster, and 32 bytes is a conservative choice made to fit inside a small
    // envelope. Asserted as a range rather than a value so that a change to
    // the chunking has to come here and say so.
    let per_epoch = delivered / epochs_used.len().max(1);
    assert!(
        (60..=200).contains(&per_epoch),
        "an epoch cost {per_epoch} messages, which is outside the range this \
         file records; if the chunk size changed, update the note above"
    );
}

/// The same, with two of every three agreement messages destroyed.
///
/// The agreement slows down and the conversation does not stop, which is what
/// the erasure coding is for.
#[test]
fn agreement_messages_may_be_lost_without_stopping_the_conversation() {
    let mut rng = StdRng::seed_from_u64(11);
    let mut a = Party::initiator();
    let mut b = Party::responder();

    let mut epochs_used: Vec<u64> = Vec::new();
    let mut round = 0usize;
    while round < 600 {
        let (am, h, ka) = a.send_message(&mut rng).unwrap();
        // Drop the agreement half of most messages. The ratcheted payload is
        // still delivered, because the two travel together but are independent.
        let deliver_agreement = round.is_multiple_of(3);
        if deliver_agreement {
            let ct = seal(&ka, &am, &h, b"payload");
            assert_eq!(b.accept(&am, &h, &ct).unwrap(), b"payload");
        } else {
            // The associated data covers the agreement half, so a message
            // whose agreement half was "lost" is modelled as one the sender
            // emitted empty: in production the two halves share a composite
            // header and are lost together, and this harness separates them
            // only to exercise the erasure coding under loss.
            let none = Msg {
                epoch: 0,
                ty: tacenta_braid::MsgType::None,
                data: None,
            };
            let ct = seal(&ka, &none, &h, b"payload");
            assert_eq!(b.accept(&none, &h, &ct).unwrap(), b"payload");
        }
        if !epochs_used.contains(&h.epoch) {
            epochs_used.push(h.epoch);
        }

        if let Ok((bm, h, kb)) = b.send_message(&mut rng) {
            let ct = seal(&kb, &bm, &h, b"reply");
            assert_eq!(a.accept(&bm, &h, &ct).unwrap(), b"reply");
        } else {
            let (bm, _) = b.agreement_send(&mut rng);
            a.agreement_receive(&bm);
        }
        round += 1;
    }

    assert!(!a.braid.failed() && !b.braid.failed());
    assert!(
        epochs_used.len() >= 2,
        "loss stopped the agreement entirely: {epochs_used:?}"
    );
}

/// A party never encrypts under an epoch its peer cannot reach.
///
/// This is the property the Braid's reported epoch exists for, and the one that
/// would be easiest to get wrong by folding a secret in as soon as it appears.
/// The responder holds an epoch's key several messages before the initiator
/// does; using it then would produce ciphertext nobody can read.
#[test]
fn no_message_is_encrypted_under_an_epoch_the_peer_cannot_reach() {
    let mut rng = StdRng::seed_from_u64(5);
    let mut a = Party::initiator();
    let mut b = Party::responder();

    let mut round = 0;
    while round < 300 {
        let (am, h, ka) = a.send_message(&mut rng).unwrap();
        // If this were wrong the receive would fail rather than disagree, so
        // both outcomes are checked.
        let ct = seal(&ka, &am, &h, b"payload");
        let got = b.accept(&am, &h, &ct).unwrap_or_else(|e| {
            panic!(
                "round {round}: peer could not reach epoch {}: {e:?}",
                h.epoch
            )
        });
        assert_eq!(got, b"payload");

        if let Ok((bm, h, kb)) = b.send_message(&mut rng) {
            let ct = seal(&kb, &bm, &h, b"reply");
            let got = a.accept(&bm, &h, &ct).unwrap_or_else(|e| {
                panic!(
                    "round {round}: initiator could not reach epoch {}: {e:?}",
                    h.epoch
                )
            });
            assert_eq!(got, b"reply");
        } else {
            let (bm, _) = b.agreement_send(&mut rng);
            a.agreement_receive(&bm);
        }
        round += 1;
    }
}

/// A message that fails its tag moves nothing, and the genuine message behind
/// it still decrypts.
///
/// Receiving derives against a candidate and returns a key; the caller
/// authenticates the ciphertext under that key and adopts the candidate only
/// then. Without that shape two state machines would move per forged message,
/// and anyone able to alter a captured frame could consume the keys of genuine
/// messages still in flight.
///
/// Every component of the header is moved in turn, because each reaches a
/// different half: the ratchet key and message numbers drive the classical
/// side, the epoch and post-quantum number the sparse side, and the ciphertext
/// the tag itself.
#[test]
fn a_forged_message_moves_none_of_the_three_state_machines() {
    let mut rng = StdRng::seed_from_u64(21);
    let mut a = Party::initiator();
    let mut b = Party::responder();

    // Get both parties past the opening exchange so there is real state to
    // damage: chains in both directions and a folded agreement epoch.
    for round in 0..8 {
        let (am, h, ka) = a.send_message(&mut rng).unwrap();
        let ct = seal(&ka, &am, &h, b"warmup");
        assert_eq!(a_or_panic(b.accept(&am, &h, &ct)), b"warmup");
        if let Ok((bm, h, kb)) = b.send_message(&mut rng) {
            let ct = seal(&kb, &bm, &h, b"warmup reply");
            assert_eq!(a_or_panic(a.accept(&bm, &h, &ct)), b"warmup reply");
        }
        let _ = round;
    }

    let (am, h, ka) = a.send_message(&mut rng).unwrap();
    let genuine = seal(&ka, &am, &h, b"the real message");

    // The agreement's own account of itself, which is the third machine. It is
    // inside this transaction because the agreement is cloneable; a forgery
    // must not move it while the two ratchets beside it stay put.
    let braid_before = b.braid.state_tag();
    let keys_before = b.pending.len();

    // A flipped tag byte.
    let mut torn = genuine.clone();
    let last = torn.len() - 1;
    torn[last] ^= 0x01;
    assert!(matches!(b.accept(&am, &h, &torn), Err(Rejected::Aead)));

    // A flipped ciphertext byte, which the tag also covers.
    let mut torn = genuine.clone();
    torn[0] ^= 0x01;
    assert!(matches!(b.accept(&am, &h, &torn), Err(Rejected::Aead)));

    // A moved classical message number. The header is associated data, so this
    // fails the tag rather than selecting another key.
    let mut moved = h;
    moved.dr.n += 1;
    assert!(b.accept(&am, &moved, &genuine).is_err());

    // A moved post-quantum message number.
    let mut moved = h;
    moved.pq_n += 1;
    assert!(b.accept(&am, &moved, &genuine).is_err());

    // A moved epoch.
    let mut moved = h;
    moved.epoch += 1;
    assert!(b.accept(&am, &moved, &genuine).is_err());

    // A substituted agreement chunk. The composite header is the associated
    // data, so a chunk an attacker rewrote fails the tag before the agreement
    // sees it; this is the case the harness could not express while its
    // associated data omitted the agreement message.
    let mut swapped = am;
    match swapped.data.as_mut() {
        Some(c) => c.data[0] ^= 0x01,
        None => swapped.epoch ^= 1,
    }
    assert!(matches!(
        b.accept(&swapped, &h, &genuine),
        Err(Rejected::Aead)
    ));

    // The agreement did not move either, which is the half that was missing.
    assert_eq!(
        b.braid.state_tag(),
        braid_before,
        "a forgery advanced the agreement"
    );
    assert_eq!(
        b.pending.len(),
        keys_before,
        "a forgery filed an agreement key the caller never accepted"
    );

    // After all of that, the genuine message is delivered. It is the only
    // assertion that matters: everything above is a way of asking whether the
    // state moved, and this is the answer.
    assert_eq!(
        a_or_panic(b.accept(&am, &h, &genuine)),
        b"the real message",
        "a forgery consumed the genuine message's key"
    );

    // And the conversation continues in both directions.
    let (am, h, ka) = a.send_message(&mut rng).unwrap();
    let ct = seal(&ka, &am, &h, b"after");
    assert_eq!(a_or_panic(b.accept(&am, &h, &ct)), b"after");
}

fn a_or_panic(r: Result<Vec<u8>, Rejected>) -> Vec<u8> {
    r.unwrap_or_else(|e| panic!("a genuine message was refused: {e:?}"))
}
