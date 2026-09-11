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
//! The model states no other persisted format, so the triple ratchet, Braid,
//! session and prekey store formats are not covered here; the conformance
//! manifest says so.

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
            "erasure-decoder-state",
            "erasure-encoder-state",
            "ratchet-state",
            "sparse-ratchet-state"
        ],
        "expected the erasure encoder's and decoder's files and the two ratchets'"
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
            _ => 5,
        };
        assert!(
            valid.len() >= floor && invalid.len() >= floor,
            "{}: checked {} accepted and {} refused",
            file.algorithm,
            valid.len(),
            invalid.len()
        );
        if file.algorithm.ends_with("ratchet-state") {
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

    eprintln!(
        "checked {total} persistence vectors in {} files",
        files.len()
    );
}
