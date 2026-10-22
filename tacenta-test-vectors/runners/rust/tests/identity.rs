//! Check tacenta-core against the identity-key vectors under vectors/identity:
//! the rule as a predicate over a table of keys (`identity-key.json`, from the
//! model), and at the two boundaries that read an identity key off the wire, a
//! prekey bundle (`bundle-admission.json`) and an initial message
//! (`initial-message-admission.json`); and identity records: the identity
//! pair digest and its verification number (`pair-digest.json`,
//! `verification-number.json`), the classification and the lookup
//! (`identity-classification.json`, `identity-lookup.json`), all from the
//! model, and initiator establishment under an expectation
//! (`initiator-expectation.json`, from `generate-identity-vectors.py`). The
//! stored formats' rows are in vectors/persistence and are checked by
//! `tests/persistence.rs`.

use std::path::Path;

#[test]
fn identity_key_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/identity");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load identity vectors");

    // Exactly these eight files: a file left out of the directory, or one
    // added without a runner for it, fails here.
    let mut algorithms: Vec<&str> = files.iter().map(|f| f.algorithm.as_str()).collect();
    algorithms.sort_unstable();
    assert_eq!(
        algorithms,
        [
            "bundle-admission",
            "identity-classification",
            "identity-key",
            "identity-lookup",
            "initial-message-admission",
            "initiator-expectation",
            "pair-digest",
            "verification-number"
        ],
        "expected exactly the eight identity vector files"
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
    assert!(count("pair-digest", "valid") >= 7);
    assert!(count("pair-digest", "invalid") >= 31);
    assert!(count("verification-number", "valid") >= 9);
    assert!(count("identity-classification", "valid") >= 11);
    assert!(count("identity-classification", "invalid") >= 9);
    assert!(count("identity-lookup", "valid") >= 11);
    assert!(count("identity-lookup", "invalid") >= 3);
    assert!(count("initiator-expectation", "valid") >= 5);
    assert!(count("initiator-expectation", "invalid") >= 39);

    // Every refusal the identity-record files name is pinned by at least one
    // vector, so a file that stopped reaching one of them fails; and the
    // digest's "either refusal conforms" is pinned in both argument orders.
    let refusals = |algorithm: &str| -> Vec<String> {
        files
            .iter()
            .filter(|f| f.algorithm == algorithm)
            .flat_map(|f| &f.vectors)
            .filter_map(|v| v.refusal.clone())
            .collect()
    };
    for (algorithm, kinds) in [
        (
            "pair-digest",
            &["decode-failure", "invalid-identity-key"][..],
        ),
        (
            "identity-classification",
            &["decode-failure", "invalid-identity-key", "malformed-record"][..],
        ),
        (
            "identity-lookup",
            &["decode-failure", "invalid-identity-key"][..],
        ),
        (
            "initiator-expectation",
            &[
                "malformed-record",
                "unexpected-identity",
                "retired-identity",
                "invalid-identity-key",
                "inconsistent-bundle",
                "non-canonical-key",
                "authentication-failure",
                "kem-input",
                "non-contributory",
            ][..],
        ),
    ] {
        let named = refusals(algorithm);
        for kind in kinds {
            assert!(
                named.iter().any(|n| n == kind),
                "{algorithm} names no {kind} refusal"
            );
        }
    }
    let either = files
        .iter()
        .filter(|f| f.algorithm == "pair-digest")
        .flat_map(|f| &f.vectors)
        .filter(|v| v.acceptable_refusals.is_some())
        .count();
    assert!(
        either >= 2,
        "pair-digest pins either refusal in both orders"
    );
    eprintln!("checked {total} identity vectors in {} files", files.len());
}
