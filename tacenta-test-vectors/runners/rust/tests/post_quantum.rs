//! Check the post-quantum crates against the vectors under vectors/post-quantum.
//!
//! These five crates were transcribed from their Lean models by hand, and the
//! transcription is what these vectors pin: a saturating subtraction versus a
//! wrapping one, two chains numbering from different starts, or a protocol
//! label that differs between model and implementation so that every derived
//! key differs with it.
//!
//! A state machine is checked by running it. A derivation is checked by its
//! bytes, and bytes are what a hand transcription can get wrong.

use std::path::Path;

#[test]
fn post_quantum_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/post-quantum");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load post-quantum vectors");
    assert!(!files.is_empty(), "expected post-quantum vector files");

    let mut total = 0;
    for file in &files {
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    // A floor over the committed post-quantum vector files; more files add to it.
    // Forty-one derivation vectors, and twenty-two for the erasure code above
    // the field (seven encoder streams, fifteen decoders).
    assert!(total >= 63, "checked {total} post-quantum vectors");
    eprintln!(
        "checked {total} post-quantum vectors across {} files",
        files.len()
    );
}
