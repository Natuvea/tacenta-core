//! Check tacenta-core's PQXDH and session-establishment paths against the
//! committed vector set. The PQXDH vectors are generated from the model
//! (`tacenta-model`, `lake exe genvectors pqxdh`); `session-e2e.json` is a
//! project-generated known answer and names its live-session source.

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

    // With and without a one-time curve prekey, plus the full byte-level flow.
    assert!(total >= 3, "checked {total} session-establishment vectors");
    eprintln!(
        "checked {total} session-establishment vectors in {} files",
        files.len()
    );
}

#[test]
fn session_end_to_end_control_rejects_wrong_associated_data() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/session-establishment");
    let mut files =
        tacenta_vectors_rust::load_dir(&dir).expect("load session-establishment vectors");
    let file = files
        .iter_mut()
        .find(|file| file.algorithm == "session-establishment-e2e")
        .expect("end-to-end session vector file");
    let fields = file.vectors[0]
        .fields
        .as_mut()
        .expect("end-to-end session vector fields");
    let ad = fields
        .get_mut("associated_data")
        .expect("associated_data field");
    ad.replace_range(0..2, if &ad[..2] == "00" { "01" } else { "00" });

    let err = tacenta_vectors_rust::check_file(file)
        .expect_err("a wrong associated-data known answer must fail the runner");
    assert!(
        err.contains("field associated_data"),
        "unexpected error: {err}"
    );
}
