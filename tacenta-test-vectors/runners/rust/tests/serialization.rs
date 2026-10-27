//! Check tacenta-core's message encoding against the vectors generated from the
//! model (tacenta-model, `lake exe genvectors serialization`), so the encoding is
//! checked against the model's byte output rather than against itself.

use std::path::Path;

#[test]
fn serialization_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/serialization");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load serialization vectors");
    assert!(!files.is_empty(), "expected serialization vector files");

    // Exactly these files: a missing one fails here rather than passing on
    // the others' counts.
    let mut algorithms: Vec<&str> = files.iter().map(|f| f.algorithm.as_str()).collect();
    algorithms.sort_unstable();
    assert_eq!(
        algorithms,
        ["frame-size", "initial-message-encoding", "message-encoding"],
        "the serialization vector files"
    );

    let mut total = 0;
    for file in &files {
        let checked = tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
        if file.algorithm == "frame-size" {
            // The size rule's file: its admitted and refused frames at both
            // bounds, the nested case, and the precedence cases with their
            // siblings one byte within the bounds (tacenta-test-vectors/README.md).
            let refused = file
                .vectors
                .iter()
                .filter(|v| v.result == "invalid")
                .count();
            assert!(
                refused >= 14 && checked - refused >= 13,
                "frame-size: {refused} refused and {} admitted vectors, expected at least 14 and 13",
                checked - refused
            );
        }
        total += checked;
    }
    assert!(
        total >= 33,
        "checked {total} serialization vectors, expected all three files"
    );
    eprintln!(
        "checked {total} serialization vectors in {} files",
        files.len()
    );
}
