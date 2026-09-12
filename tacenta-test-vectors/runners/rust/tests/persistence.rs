//! Check tacenta-core's persisted formats against the vectors generated from
//! the model (tacenta-model, `Model.Erasure` and `Model.PersistedState`):
//! the bytes a state built by operations is written as, that those bytes read
//! back to a state written the same way, which stored bytes the readers accept
//! and what they hold, and which they refuse and with which refusal
//! (tacenta-spec/protocol/session-persistence.md: Ratchet state, Sparse
//! ratchet state, Erasure coder sub-formats, Semantic rules of the leaf
//! formats, Rejection).
//!
//! The erasure coders' states are built by `tacenta-erasure`'s own operations
//! and compared as coders. The two ratchets' states are built by replaying the
//! vector's operations on `tacenta-ratchet` and `tacenta-spqr` from the same
//! starting point the model used -- a fresh state, or stored bytes the reader
//! accepts -- and compared by the bytes they are written as, since neither
//! crate exposes a state's fields or compares two states outside its own
//! tests.
//!
//! The Triple Ratchet's and the Braid's states are covered here too: the
//! Triple Ratchet's by replaying its own `send`/`receive` and by stored bytes,
//! and the Braid's by stored bytes plus the two transitions out of
//! `Ct2Sampled` that read no KEM value.
//!
//! The prekey store's stored format is covered by stored bytes alone. Its four
//! accepted vectors carry bytes `tacenta-core` itself produced, because the
//! model has no signatures and so cannot build a store whose stored signatures
//! verify; its thirteen refusals are one field of those bytes changed, so each
//! is refused for the rule under test rather than for a signature that never
//! verified. The session has no model and is not covered; the conformance
//! manifest says so, and says which Braid tags the vectors reach and why the
//! rest do not.

use std::path::Path;

#[test]
fn persistence_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/persistence");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load persistence vectors");
    let mut algorithms: Vec<&str> = files.iter().map(|f| f.algorithm.as_str()).collect();
    algorithms.sort_unstable();
    assert_eq!(
        algorithms,
        [
            "braid-state",
            "erasure-decoder-state",
            "erasure-encoder-state",
            "prekey-store-state",
            "ratchet-state",
            "sparse-ratchet-state",
            "triple-ratchet-state"
        ],
        "expected the erasure coders' two files and the four persisted states"
    );

    let mut total = 0;
    for file in &files {
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    for file in &files {
        let (valid, invalid): (Vec<_>, Vec<_>) =
            file.vectors.iter().partition(|v| v.result == "valid");
        let floor = match file.algorithm.as_str() {
            "ratchet-state" | "sparse-ratchet-state" => 20,
            "braid-state" => 9,
            "prekey-store-state" => 4,
            "triple-ratchet-state" => 8,
            _ => 5,
        };
        assert!(
            valid.len() >= floor && invalid.len() >= floor,
            "{}: checked {} accepted and {} refused",
            file.algorithm,
            valid.len(),
            invalid.len()
        );
        if file.algorithm.ends_with("ratchet-state") || file.algorithm == "braid-state" {
            assert!(
                invalid.iter().all(|v| v.refusal.is_some()),
                "{}: every refused state names its refusal",
                file.algorithm
            );
        }
        eprintln!(
            "{}: {} accepted, {} refused",
            file.algorithm,
            valid.len(),
            invalid.len()
        );
    }
    // The counters' ceilings (ratchet.md, Sending and receiving and Skipped
    // keys; sparse-pq-ratchet.md, Sending and Receiving; session-persistence.md,
    // Principles). `check_file` above has already replayed each of these on
    // `tacenta-ratchet` and `tacenta-spqr`: the clock staying at its stop
    // written as the model writes it, and each step past a ceiling refused
    // with `ChainExhausted`. This holds the files to carrying them, so a
    // regeneration that dropped one fails here rather than passing on fewer.
    let ceilings: [(&str, &[&str], &[&str]); 2] = [
        (
            "ratchet-state",
            &[
                "clock-stays-at-its-stop",
                "clock-stays-at-its-stop-on-the-chain",
            ],
            &["send-at-u32-max-refused", "receive-at-nr-u32-max-refused"],
        ),
        (
            "sparse-ratchet-state",
            &[],
            &[
                "advance-onto-u64-max-refused",
                "send-past-u64-max-refused",
                "receive-past-u64-max-refused",
            ],
        ),
    ];
    for (algorithm, stays, refused) in ceilings {
        let file = files
            .iter()
            .find(|f| f.algorithm == algorithm)
            .expect("the file is loaded");
        let vector = |id: &str| {
            file.vectors
                .iter()
                .find(|v| v.id == id)
                .unwrap_or_else(|| panic!("{algorithm}: no vector {id}"))
        };
        for id in stays {
            let v = vector(id);
            assert!(
                v.result == "valid" && v.inputs.contains_key("steps"),
                "{algorithm}: {id} is operations the model and the crate both take"
            );
        }
        for id in refused {
            let v = vector(id);
            assert!(
                v.result == "invalid"
                    && v.inputs.contains_key("steps")
                    && v.refusal.as_deref() == Some("counter-exhaustion"),
                "{algorithm}: {id} is operations whose last step is refused as counter exhaustion"
            );
        }
    }

    // The Braid's epoch ceiling, which until these vectors existed no vector
    // pinned (session-persistence.md, Principles; mlkem-braid.md, Failure).
    // The reader's half is the reserved epoch; the transitions' half is the
    // pair of `Ct2Sampled` steps, the one place a stored Braid can be driven
    // without a KEM value.
    let braid = files
        .iter()
        .find(|f| f.algorithm == "braid-state")
        .expect("the Braid's file is loaded");
    let braid_vector = |id: &str| {
        braid
            .vectors
            .iter()
            .find(|v| v.id == id)
            .unwrap_or_else(|| panic!("braid-state: no vector {id}"))
    };
    let reserved = braid_vector("epoch-u64-max");
    assert!(
        reserved.result == "invalid" && reserved.refusal.as_deref() == Some("short-or-malformed"),
        "braid-state: a stored epoch of u64::MAX is refused"
    );
    for id in [
        "ct2-sampled-below-the-ceiling-steps",
        "ct2-sampled-at-the-ceiling-fails",
    ] {
        let v = braid_vector(id);
        assert!(
            v.result == "valid" && v.inputs.contains_key("start") && v.inputs.contains_key("steps"),
            "braid-state: {id} is a stored state the vector drives a message through"
        );
    }
    // The two fields whose layout the page delegates (ADR-0006, point 5) are
    // held to their length and nothing else, which is the part of their rule
    // a reader without `libcrux-ml-kem` can apply.
    for id in ["key-pair-wrong-length", "encaps-wrong-length"] {
        let v = braid_vector(id);
        assert!(
            v.result == "invalid" && v.refusal.as_deref() == Some("short-or-malformed"),
            "braid-state: {id} is refused"
        );
    }
    // And no accepted vector carries a key pair. The page's content clause for
    // tags 1 to 4 reaches inside one, and is scoped to a reader that knows the
    // delegated layout; the model is outside that scope, so it checks the
    // field's length, accepts it, and conforms, while `tacenta-braid` has the
    // layout and checks the content too. A state that fails the clause is
    // therefore refused by one conforming reader and accepted by another, so
    // no vector can carry one: there is no single verdict to pin.
    for v in braid.vectors.iter().filter(|v| v.result == "valid") {
        if let Some(hex_bytes) = v.inputs.get("bytes") {
            let raw = hex::decode(hex_bytes).expect("braid-state: bytes are hex");
            let tag = raw.get(1).copied().unwrap_or(0xff);
            assert!(
                !(1..=4).contains(&tag),
                "braid-state: {} is an accepted state with tag {tag}, which carries a key pair \
                 the model checks only the length of",
                v.id
            );
        }
    }

    // The refusal the specification gained for this phase: a half whose own
    // version byte its own reader does not recognise is short or malformed,
    // not a wrong version (session-persistence.md, Triple ratchet state).
    let triple = files
        .iter()
        .find(|f| f.algorithm == "triple-ratchet-state")
        .expect("the Triple Ratchet's file is loaded");
    for id in [
        "classical-half-with-an-unknown-version",
        "sparse-half-with-an-unknown-version",
        "halves-disagree-on-the-role",
    ] {
        let v = triple
            .vectors
            .iter()
            .find(|v| v.id == id)
            .unwrap_or_else(|| panic!("triple-ratchet-state: no vector {id}"));
        assert!(
            v.result == "invalid" && v.refusal.as_deref() == Some("short-or-malformed"),
            "triple-ratchet-state: {id} is refused as short or malformed"
        );
    }

    eprintln!(
        "checked {total} persistence vectors in {} files",
        files.len()
    );
}
