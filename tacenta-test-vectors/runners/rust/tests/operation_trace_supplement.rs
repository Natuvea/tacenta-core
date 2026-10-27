//! The operation-trace supplement (`traces/session-operation-trace-supplement.json`, schema version 2;
//! `session-operation-trace-supplement.md`), driven through tacenta-core.
//!
//! The supplement is not independently authored (its `provenance` says so), and the independent operation
//! reader does not read it. This is its only semantic consumer: for every trace it builds the fixtures the
//! trace names with real sessions and a real prekey store, performs each step's operation, and compares what
//! happened with what the step declares:
//!
//! * the outcome, and the refusal name where the step gives one (`PlaintextTooLong`, `AgreementFailed`, and
//!   `decode-failure` for any `Decode` error, the size rule's included);
//! * `prekey_store` and `session`: `unchanged` means the stored bytes (`PrekeyStore::to_bytes`,
//!   `Session::export`) are byte-equal before and after; any other value means they changed (for
//!   `responder-established`, that a session was returned). The finer responder fields (`one_time_curve`,
//!   `one_time_kem`, `last_resort_record`) are checked as part of the store's bytes: `unchanged` needs the
//!   store unchanged, `deleted` needs it changed;
//! * `random_draws: none`: the operation made no call to the random source.
//!
//! The trace ids are enumerated: a trace this file does not drive, or a driven trace missing from the file,
//! fails. Every trace must agree with tacenta-core except the `control-` traces, which must disagree; that is
//! the check that this consumer can fail.

use std::collections::BTreeMap;
use std::path::Path;

use rand_core::{CryptoRng, RngCore};
use serde::Deserialize;
use tacenta_core::serialization::{
    MAX_INITIAL_FRAME_LEN, MAX_PLAINTEXT_LEN, MAX_RATCHET_FRAME_LEN, decode_initial, encode_initial,
};
use tacenta_core::sessions::{
    Expectation, Identity, LifecycleError, PrekeyStore, Session, establish_initiator,
    establish_responder,
};

#[derive(Deserialize)]
struct Document {
    schema_version: u32,
    algorithm: String,
    provenance: String,
    traces: Vec<Trace>,
}

#[derive(Deserialize)]
struct Trace {
    id: String,
    steps: Vec<Step>,
}

#[derive(Deserialize)]
struct Step {
    op: String,
    inputs: BTreeMap<String, String>,
    expect: Expect,
    effect: BTreeMap<String, String>,
}

#[derive(Deserialize)]
struct Expect {
    outcome: String,
    refusal: Option<String>,
}

/// A deterministic stream that counts the calls made to it. Not random; a fixture source.
struct Stream {
    state: u64,
    calls: usize,
}

impl Stream {
    fn new(seed: u64) -> Stream {
        Stream {
            state: seed,
            calls: 0,
        }
    }
    fn word(&mut self) -> u64 {
        // splitmix64
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

impl RngCore for Stream {
    fn next_u32(&mut self) -> u32 {
        self.calls += 1;
        self.word() as u32
    }
    fn next_u64(&mut self) -> u64 {
        self.calls += 1;
        self.word()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.calls += 1;
        for chunk in dest.chunks_mut(8) {
            let w = self.word().to_le_bytes();
            chunk.copy_from_slice(&w[..chunk.len()]);
        }
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

// A fixture source, as the comment on `Stream` says.
impl CryptoRng for Stream {}

/// What one operation did.
#[derive(Debug)]
struct Observed {
    refusal: Option<&'static str>,
    store_changed: bool,
    session_changed: bool,
    draws: usize,
}

fn refusal_name(e: &LifecycleError) -> &'static str {
    match e {
        LifecycleError::PlaintextTooLong => "PlaintextTooLong",
        LifecycleError::AgreementFailed => "AgreementFailed",
        LifecycleError::Decode(_) => "decode-failure",
        LifecycleError::NotARepeatedInitial => "NotARepeatedInitial",
        LifecycleError::Aead => "authentication-failure",
        _ => "other",
    }
}

/// `send` of `len` bytes on `session`.
fn send(session: &mut Session, len: usize, rng: &mut Stream) -> Observed {
    let before = session.export().to_vec();
    let calls = rng.calls;
    let result = session.encrypt(&vec![0x5a; len], rng);
    Observed {
        refusal: result.as_ref().err().map(refusal_name),
        store_changed: false,
        session_changed: session.export().as_slice() != before.as_slice(),
        draws: rng.calls - calls,
    }
}

/// `receive` (or `receive-repeated-initial`) of `frame` on `session`.
fn receive(session: &mut Session, frame: &[u8], rng: &mut Stream) -> Observed {
    let before = session.export().to_vec();
    let calls = rng.calls;
    let result = session.decrypt(frame, rng);
    Observed {
        refusal: result.as_ref().err().map(refusal_name),
        store_changed: false,
        session_changed: session.export().as_slice() != before.as_slice(),
        draws: rng.calls - calls,
    }
}

/// `establish-responder` of `frame` on `store`.
fn establish(
    bob: &Identity,
    store: &mut PrekeyStore,
    frame: &[u8],
    rng: &mut Stream,
) -> (Observed, Option<Session>) {
    let before = store.to_bytes().to_vec();
    let calls = rng.calls;
    let result = establish_responder(bob, store, frame, rng);
    let observed = Observed {
        refusal: result.as_ref().err().map(refusal_name),
        store_changed: store.to_bytes().as_slice() != before.as_slice(),
        session_changed: result.is_ok(),
        draws: rng.calls - calls,
    };
    (observed, result.ok().map(|(s, _)| s))
}

/// Two parties: Alice pending after her first initial message, Bob established from it.
struct Pair {
    alice: Session,
    bob: Session,
}

fn pair(rng: &mut Stream) -> Pair {
    let alice_id = Identity::generate(rng);
    let bob_id = Identity::generate(rng);
    let mut store = bob_id.create_prekeys(2, rng);
    let bundle = store.publish();
    let mut alice = establish_initiator(&alice_id, &bundle, &Expectation::first_contact(&[]), rng)
        .expect("fixture: establish the initiator");
    let initial = alice
        .encrypt(b"first", rng)
        .expect("fixture: first message");
    let (bob, _) =
        establish_responder(&bob_id, &mut store, &initial, rng).expect("fixture: responder");
    Pair { alice, bob }
}

/// Bob's session after an authenticated receive moved its Braid to Failed: one bit of its stored Braid MAC key
/// flipped, then Alice's messages delivered until the header completes on his side.
fn failed(p: &mut Pair, rng: &mut Stream) -> Session {
    let mut saved = p.bob.export().to_vec();
    let triple_len = u32::from_be_bytes(saved[1..5].try_into().expect("four bytes")) as usize;
    let braid = 1 + 4 + triple_len + 4;
    saved[braid + 2 + 8 + 32] ^= 0x01;
    let mut bob = Session::import(&saved).expect("fixture: import");
    let mut i = 0u8;
    while !bob.agreement_failed() {
        let m = p.alice.encrypt(&[i], rng).expect("fixture: send");
        bob.decrypt(&m, rng)
            .expect("fixture: accepted until the refusals begin");
        i += 1;
        assert!(i < 8, "fixture: the agreement did not fail");
    }
    bob
}

fn padded(frame: &[u8], len: usize) -> Vec<u8> {
    let mut out = frame.to_vec();
    out.resize(len, 0);
    out
}

fn length(step: &Step) -> usize {
    step.inputs["plaintext_length"]
        .parse()
        .expect("plaintext_length is a decimal string")
}

/// Perform a trace's steps and return what each did, in order. Each arm builds the fixtures the trace's
/// `fixtures` describe.
fn drive(trace: &Trace) -> Vec<Observed> {
    let mut rng = Stream::new(0x7472_6163_6573);
    let s = &trace.steps;
    match trace.id.as_str() {
        "send-plaintext-too-long-pending-and-established" => {
            let alice_id = Identity::generate(&mut rng);
            let bob_id = Identity::generate(&mut rng);
            let mut store = bob_id.create_prekeys(2, &mut rng);
            let bundle = store.publish();
            let mut alice = establish_initiator(
                &alice_id,
                &bundle,
                &Expectation::first_contact(&[]),
                &mut rng,
            )
            .expect("establish the initiator");
            let first = send(&mut alice, length(&s[0]), &mut rng);
            let initial = alice.encrypt(b"first", &mut rng).expect("first message");
            let (mut bob, _) =
                establish_responder(&bob_id, &mut store, &initial, &mut rng).expect("responder");
            let reply = bob.encrypt(b"reply", &mut rng).expect("reply");
            alice.decrypt(&reply, &mut rng).expect("reply decrypts");
            let second = send(&mut alice, length(&s[1]), &mut rng);
            let third = send(&mut alice, length(&s[2]), &mut rng);
            vec![first, second, third]
        }
        "control-plaintext-too-long-wrongly-accepted" => {
            let mut p = pair(&mut rng);
            let reply = p.bob.encrypt(b"reply", &mut rng).expect("reply");
            p.alice.decrypt(&reply, &mut rng).expect("reply decrypts");
            vec![send(&mut p.alice, length(&s[0]), &mut rng)]
        }
        "send-plaintext-too-long-before-agreement-failed" => {
            let mut p = pair(&mut rng);
            let mut bob = failed(&mut p, &mut rng);
            let first = send(&mut bob, length(&s[0]), &mut rng);
            let second = send(&mut bob, length(&s[1]), &mut rng);
            vec![first, second]
        }
        "establish-responder-frame-too-long" => {
            let alice_id = Identity::generate(&mut rng);
            let bob_id = Identity::generate(&mut rng);
            let mut store = bob_id.create_prekeys(2, &mut rng);
            let bundle = store.publish();
            let mut alice = establish_initiator(
                &alice_id,
                &bundle,
                &Expectation::first_contact(&[]),
                &mut rng,
            )
            .expect("establish the initiator");
            let initial = alice.encrypt(b"first", &mut rng).expect("first message");
            let oversized = padded(&initial, MAX_INITIAL_FRAME_LEN + 1);
            let (first, _) = establish(&bob_id, &mut store, &oversized, &mut rng);
            let (second, _) = establish(&bob_id, &mut store, &initial, &mut rng);
            vec![first, second]
        }
        "receive-ratchet-frame-too-long" => {
            let mut p = pair(&mut rng);
            let reply = p.bob.encrypt(b"reply", &mut rng).expect("reply");
            p.alice.decrypt(&reply, &mut rng).expect("reply decrypts");
            let next = p.alice.encrypt(b"next", &mut rng).expect("next");
            let oversized = padded(&next, MAX_RATCHET_FRAME_LEN + 1);
            let first = receive(&mut p.bob, &oversized, &mut rng);
            let second = receive(&mut p.bob, &next, &mut rng);
            vec![first, second]
        }
        "receive-repeated-initial-nested-too-long" => {
            let mut p = pair(&mut rng);
            let repeat = p.alice.encrypt(b"repeat", &mut rng).expect("repeat");
            let d = decode_initial(&repeat).expect("the repeat decodes");
            let inner = padded(&d.message, MAX_RATCHET_FRAME_LEN + 1);
            let nested = encode_initial(
                &d.identity,
                &d.ephemeral,
                &[],
                d.signed_prekey_id,
                d.one_time_prekey_id,
                d.kem_prekey_id,
                &inner,
            );
            assert!(
                nested.len() <= MAX_INITIAL_FRAME_LEN,
                "within the outer bound"
            );
            let first = receive(&mut p.bob, &nested, &mut rng);
            let second = receive(&mut p.bob, &repeat, &mut rng);
            vec![first, second]
        }
        "receive-frame-too-long-before-agreement-failed" => {
            let mut p = pair(&mut rng);
            let mut bob = failed(&mut p, &mut rng);
            let repeat = p.alice.encrypt(b"repeat", &mut rng).expect("repeat");
            let oversized = padded(&repeat, MAX_INITIAL_FRAME_LEN + 1);
            let first = receive(&mut bob, &oversized, &mut rng);
            let second = receive(&mut bob, &repeat, &mut rng);
            vec![first, second]
        }
        other => panic!("operation_trace_supplement: no driver for trace {other}"),
    }
}

/// The differences between what a step declares and what happened; empty when they agree.
fn compare(step: &Step, seen: &Observed) -> Vec<String> {
    let mut out = Vec::new();
    let refused = seen.refusal.is_some();
    match step.expect.outcome.as_str() {
        "ok" if refused => out.push(format!("declared ok, refused as {:?}", seen.refusal)),
        "refused" if !refused => out.push("declared refused, accepted".to_string()),
        _ => {}
    }
    if let Some(want) = &step.expect.refusal
        && seen.refusal != Some(want.as_str())
    {
        out.push(format!("declared refusal {want}, saw {:?}", seen.refusal));
    }
    for (field, value) in &step.effect {
        let ok = match field.as_str() {
            "prekey_store" | "one_time_curve" | "one_time_kem" | "last_resort_record" => {
                (value == "unchanged") != seen.store_changed
            }
            "session" => (value == "unchanged") != seen.session_changed,
            "random_draws" => value == "none" && seen.draws == 0,
            _ => false,
        };
        if !ok {
            out.push(format!(
                "declared {field} {value}, saw store changed {}, session changed {}, {} draws",
                seen.store_changed, seen.session_changed, seen.draws
            ));
        }
    }
    out
}

#[test]
fn the_supplement_traces_agree_with_tacenta_core() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../traces/session-operation-trace-supplement.json");
    let text = std::fs::read_to_string(&path).expect("read the supplement");
    let doc: Document = serde_json::from_str(&text).expect("parse the supplement");
    assert_eq!(doc.schema_version, 2);
    assert_eq!(doc.algorithm, "session-operation-trace-supplement");
    assert!(
        doc.provenance.contains("Not independently authored"),
        "the supplement must say it is not independently authored"
    );

    // Exactly these traces, so a dropped one fails here.
    let mut ids: Vec<&str> = doc.traces.iter().map(|t| t.id.as_str()).collect();
    ids.sort_unstable();
    assert_eq!(
        ids,
        [
            "control-plaintext-too-long-wrongly-accepted",
            "establish-responder-frame-too-long",
            "receive-frame-too-long-before-agreement-failed",
            "receive-ratchet-frame-too-long",
            "receive-repeated-initial-nested-too-long",
            "send-plaintext-too-long-before-agreement-failed",
            "send-plaintext-too-long-pending-and-established",
        ],
        "the supplement's traces"
    );
    assert_eq!(
        MAX_PLAINTEXT_LEN, 1_048_575,
        "the traces' plaintext lengths"
    );

    let mut steps = 0;
    for trace in &doc.traces {
        let seen = drive(trace);
        assert_eq!(
            seen.len(),
            trace.steps.len(),
            "{}: one result per step",
            trace.id
        );
        let problems: Vec<String> = trace
            .steps
            .iter()
            .zip(&seen)
            .enumerate()
            .flat_map(|(i, (step, obs))| {
                compare(step, obs)
                    .into_iter()
                    .map(move |p| format!("step {i} ({}): {p}", step.op))
            })
            .collect();
        if trace.id.starts_with("control-") {
            assert!(
                !problems.is_empty(),
                "{}: a control trace must disagree with tacenta-core",
                trace.id
            );
        } else {
            assert!(problems.is_empty(), "{}: {problems:#?}", trace.id);
        }
        steps += trace.steps.len();
    }
    eprintln!(
        "operation-trace supplement: {} traces, {steps} steps, agreed (the control disagreed)",
        doc.traces.len()
    );
}
