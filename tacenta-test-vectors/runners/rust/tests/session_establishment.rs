//! Check tacenta-core's PQXDH shared-secret derivation against the vectors
//! generated from the model (tacenta-model, `lake exe genvectors pqxdh`), so the
//! implementation is checked against the model's byte output rather than against
//! itself.

use std::path::Path;

#[test]
fn session_establishment_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/session-establishment");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load session-establishment vectors");
    assert!(
        !files.is_empty(),
        "expected session-establishment vector files"
    );

    let mut total = 0;
    for file in &files {
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    // With and without a one-time curve prekey.
    assert!(total >= 2, "checked {total} session-establishment vectors");
    eprintln!(
        "checked {total} session-establishment vectors in {} files",
        files.len()
    );
}
