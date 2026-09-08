//! Check tacenta-core against the primitive vectors under vectors/primitives.

use std::path::Path;

#[test]
fn primitive_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/primitives");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load primitive vectors");
    assert!(!files.is_empty(), "expected primitive vector files");

    let mut total = 0;
    for file in &files {
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    // hkdf (2) + hmac (2) + x25519 (2) + ed25519 (2).
    assert!(total >= 8, "checked {total} primitive vectors");
    eprintln!(
        "checked {total} primitive vectors across {} files",
        files.len()
    );
}
