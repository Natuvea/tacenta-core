//! Replay the Double Ratchet protocol vectors against tacenta-core. The vectors
//! are generated from the model (tacenta-model, `lake exe genvectors`), so this
//! checks the implementation reproduces the model's message keys byte for byte.

use std::path::Path;

#[test]
fn ratchet_vectors_pass() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    // Model-generated scenarios plus the hand-authored malformed-input rejection.
    let mut files = tacenta_vectors_rust::load_ratchet_dir(&root.join("../../vectors/ratchet"))
        .expect("load ratchet vectors");
    files.extend(
        tacenta_vectors_rust::load_ratchet_dir(&root.join("../../vectors/malformed-input"))
            .expect("load malformed-input vectors"),
    );
    assert!(!files.is_empty(), "expected ratchet vector files");

    let mut total = 0;
    let mut vectors = 0;
    for file in &files {
        vectors += file.vectors.len();
        total += tacenta_vectors_rust::check_ratchet_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    assert!(vectors >= 4, "checked {vectors} ratchet vectors");
    eprintln!(
        "checked {total} ratchet steps across {vectors} vectors in {} files",
        files.len()
    );
}
