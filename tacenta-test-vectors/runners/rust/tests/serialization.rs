//! Check tacenta-core's message encoding against the vectors generated from the
//! model (tacenta-model, `lake exe genvectors serialization`), so the encoding is
//! checked against the model's byte output rather than against itself.

use std::path::Path;

#[test]
fn serialization_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/serialization");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load serialization vectors");
    assert!(!files.is_empty(), "expected serialization vector files");

    let mut total = 0;
    for file in &files {
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    // Both files, not just one: a count that only covers the ratchet messages
    // would still pass if the initial-message file were dropped.
    assert!(
        total >= 6,
        "checked {total} serialization vectors, expected both files"
    );
    eprintln!(
        "checked {total} serialization vectors in {} files",
        files.len()
    );
}
