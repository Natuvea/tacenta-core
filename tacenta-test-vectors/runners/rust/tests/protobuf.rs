//! Check tacenta-core's bounded protobuf profile readers against the vectors
//! generated from the model (tacenta-model, `Model.Protobuf`), both accepted
//! regions, with the fields they decode to, and refused ones
//! (tacenta-spec/protocol/protobuf-profile.md).

use std::path::Path;

#[test]
fn protobuf_vectors_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/protobuf");
    let files = tacenta_vectors_rust::load_dir(&dir).expect("load protobuf vectors");
    assert_eq!(files.len(), 2, "expected both message types' files");

    let mut total = 0;
    for file in &files {
        total += tacenta_vectors_rust::check_file(file)
            .unwrap_or_else(|e| panic!("{}: {e}", file.algorithm));
    }

    // Refusals are half of what the profile says, so both kinds are counted:
    // a file that lost its invalid vectors would still pass every check above.
    let (valid, invalid): (Vec<_>, Vec<_>) = files
        .iter()
        .flat_map(|f| f.vectors.iter())
        .partition(|v| v.result == "valid");
    assert!(
        valid.len() >= 13,
        "checked {} accepted regions",
        valid.len()
    );
    assert!(
        invalid.len() >= 29,
        "checked {} refused regions",
        invalid.len()
    );
    eprintln!(
        "checked {total} protobuf vectors ({} accepted, {} refused) in {} files",
        valid.len(),
        invalid.len(),
        files.len()
    );
}
