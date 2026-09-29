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

    // Exactly the vectors each file holds, so that a file that loses one fails
    // here rather than passing on fewer: hkdf (2 RFC 5869), hmac (2 RFC 4231
    // and the replay-identity construction's known answer), x25519 (2 RFC 7748
    // and 6 low-order refusals), ed25519 (2 RFC 8032), xeddsa (3 signing and 20
    // verify-only, three of them under keys of mixed order).
    let expected = [
        ("hkdf-sha256", 2),
        ("hmac-sha256", 3),
        ("x25519", 8),
        ("ed25519", 2),
        ("xeddsa", 23),
    ];
    for (algorithm, count) in expected {
        let file = files
            .iter()
            .find(|f| f.algorithm == algorithm)
            .unwrap_or_else(|| panic!("no {algorithm} primitive file"));
        assert_eq!(
            file.vectors.len(),
            count,
            "{algorithm}: vectors in the file"
        );
    }
    assert_eq!(files.len(), expected.len(), "primitive files");
    assert_eq!(total, 38, "checked {total} primitive vectors");
    eprintln!(
        "checked {total} primitive vectors across {} files",
        files.len()
    );
}
