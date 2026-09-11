//! Check tacenta-core's decoders against the model-generated decoder files under
//! vectors/malformed-input: each accepts a curve key in its canonical spelling
//! and refuses it re-spelled, in every position it reads one (message-format.md,
//! Curve public keys). The Double Ratchet scenario file in the same directory
//! is replayed by `tests/ratchet.rs`.

use std::path::Path;

#[test]
fn malformed_input_decoder_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/malformed-input");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load malformed-input vectors");

    let mut total = 0;
    let mut refused = 0;
    for file in &files {
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
        refused += file
            .vectors
            .iter()
            .filter(|v| v.result == "invalid")
            .count();
    }

    // All three decoders, not some: the composite header's dh (three refused
    // spellings: bit 255 set, 9 + p, and p itself), the bundle's three keys
    // (three each), and the initial message's identity and ephemeral (three
    // each).
    let mut algorithms: Vec<&str> = files.iter().map(|f| f.algorithm.as_str()).collect();
    algorithms.sort_unstable();
    assert_eq!(
        algorithms,
        [
            "composite-header-decode",
            "initial-message-decode",
            "prekey-bundle-decode"
        ],
        "expected all three decoder files"
    );
    assert!(refused >= 18, "checked {refused} refusals, expected 18");

    // A key exactly p in every position, since a decoder that refuses only
    // values above p passes every other vector here.
    for (algorithm, positions) in [
        ("composite-header-decode", 1),
        ("prekey-bundle-decode", 3),
        ("initial-message-decode", 2),
    ] {
        let at_p = files
            .iter()
            .filter(|f| f.algorithm == algorithm)
            .flat_map(|f| &f.vectors)
            .filter(|v| v.result == "invalid" && v.id.ends_with("-equal-to-p"))
            .count();
        assert!(
            at_p >= positions,
            "{algorithm}: {at_p} refusals of a key exactly p, expected {positions}"
        );
    }
    eprintln!(
        "checked {total} malformed-input decoder vectors, {refused} of them refusals, in {} files",
        files.len()
    );
}
