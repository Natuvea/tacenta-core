//! Check tacenta-core against the identity-key vectors under vectors/identity:
//! the rule as a predicate over a table of keys (`identity-key.json`, from the
//! model), and at the two boundaries that read an identity key off the wire, a
//! prekey bundle (`bundle-admission.json`) and an initial message
//! (`initial-message-admission.json`). The stored formats' rows are in
//! vectors/persistence and are checked by `tests/persistence.rs`.

use std::path::Path;

#[test]
fn identity_key_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/identity");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load identity vectors");

    // Exactly these three files: a file left out of the directory, or one
    // added without a runner for it, fails here.
    let mut algorithms: Vec<&str> = files.iter().map(|f| f.algorithm.as_str()).collect();
    algorithms.sort_unstable();
    assert_eq!(
        algorithms,
        [
            "bundle-admission",
            "identity-key",
            "initial-message-admission"
        ],
        "expected exactly the three identity vector files"
    );

    let mut total = 0;
    for file in &files {
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    // Per-file floors, and the counts of each verdict, so an emptied file or a
    // file that stopped refusing fails.
    let count = |algorithm: &str, result: &str| {
        files
            .iter()
            .filter(|f| f.algorithm == algorithm)
            .flat_map(|f| &f.vectors)
            .filter(|v| v.result == result)
            .count()
    };
    assert!(
        count("identity-key", "valid") >= 6,
        "identity-key admits at least six keys"
    );
    assert!(
        count("identity-key", "invalid") >= 30,
        "identity-key refuses at least thirty keys"
    );
    assert!(count("bundle-admission", "valid") >= 1);
    assert!(count("bundle-admission", "invalid") >= 9);
    assert!(count("initial-message-admission", "valid") >= 1);
    assert!(count("initial-message-admission", "invalid") >= 10);
    eprintln!("checked {total} identity vectors in {} files", files.len());
}
