//! Check tacenta-erasure's persisted encoder and decoder formats against the
//! vectors generated from the model (tacenta-model, `Model.Erasure`): the
//! bytes a coder built by operations is written as, that those bytes read back
//! to the same coder, and which stored bytes the readers refuse
//! (tacenta-spec/protocol/session-persistence.md, Erasure coder sub-formats).
//!
//! These are the only persisted formats with vectors. The model states no
//! other, so the ratchet, sparse ratchet, triple ratchet, Braid, session and
//! prekey store formats are not covered here; the conformance manifest says so.

use std::path::Path;

#[test]
fn persistence_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/persistence");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load persistence vectors");
    assert_eq!(
        files.len(),
        2,
        "expected the encoder's and the decoder's files"
    );

    let mut total = 0;
    for file in &files {
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    let (valid, invalid): (Vec<_>, Vec<_>) = files
        .iter()
        .flat_map(|f| f.vectors.iter())
        .partition(|v| v.result == "valid");
    assert!(valid.len() >= 13, "checked {} accepted states", valid.len());
    assert!(
        invalid.len() >= 13,
        "checked {} refused states",
        invalid.len()
    );
    eprintln!(
        "checked {total} persistence vectors ({} accepted, {} refused) in {} files",
        valid.len(),
        invalid.len(),
        files.len()
    );
}
