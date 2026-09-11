//! Check tacenta-core's AEAD against the vectors under vectors/aead
//! (tacenta-spec/protocol/message-format.md, Authenticated encryption).
//!
//! The model has no AES. The files are generated from the model's HMAC and the
//! section's padding and receiver steps, with every AES-256 block value taken
//! from NIST SP 800-38A, and their `source` field says so. So what these
//! vectors check against is a published standard and the model, and not this
//! implementation's own output.

use std::path::Path;

#[test]
fn aead_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/aead");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load AEAD vectors");
    assert_eq!(files.len(), 2, "expected the encrypt and decrypt files");

    let mut total = 0;
    for file in &files {
        assert!(
            file.source.contains("NIST SP 800-38A"),
            "{}: the source must say where the AES block values come from",
            file.algorithm
        );
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    let (valid, invalid): (Vec<_>, Vec<_>) = files
        .iter()
        .flat_map(|f| f.vectors.iter())
        .partition(|v| v.result == "valid");
    assert!(valid.len() >= 7, "checked {} accepted vectors", valid.len());
    assert!(invalid.len() >= 10, "checked {} refusals", invalid.len());
    eprintln!(
        "checked {total} AEAD vectors ({} accepted, {} refused) in {} files",
        valid.len(),
        invalid.len(),
        files.len()
    );
}
