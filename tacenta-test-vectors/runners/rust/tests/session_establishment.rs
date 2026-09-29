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

fn e2e_file() -> tacenta_vectors_rust::VectorFile {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vectors/session-establishment");
    tacenta_vectors_rust::load_dir(&dir)
        .expect("load session-establishment vectors")
        .into_iter()
        .find(|file| file.algorithm == "session-establishment-e2e")
        .expect("end-to-end session vector file")
}

/// Both end-to-end vectors exist under their names, so a regeneration that
/// dropped one fails here rather than passing on fewer.
#[test]
fn the_end_to_end_file_holds_both_vectors() {
    let ids: Vec<_> = e2e_file().vectors.into_iter().map(|v| v.id).collect();
    assert_eq!(
        ids,
        [
            "one-time-prekeys-first-message",
            "last-resort-first-message"
        ]
    );
}

/// Every named output is compared in full: change the first byte of any one
/// field, in either vector, and the runner fails and names that field. The
/// runner recomputes each field from the inputs, so a field it merely echoed
/// would survive this.
#[test]
fn session_end_to_end_runner_compares_every_field() {
    let mut file = e2e_file();
    let mut swept = 0;
    for index in 0..file.vectors.len() {
        let names: Vec<String> = file.vectors[index]
            .fields
            .as_ref()
            .expect("end-to-end session vector fields")
            .keys()
            .cloned()
            .collect();
        for name in names {
            let original = {
                let value = file.vectors[index]
                    .fields
                    .as_mut()
                    .unwrap()
                    .get_mut(&name)
                    .unwrap();
                let original = value[..2].to_owned();
                value.replace_range(0..2, if &value[..2] == "00" { "01" } else { "00" });
                original
            };
            let err = tacenta_vectors_rust::check_file(&file)
                .expect_err("a wrong known answer must fail the runner");
            assert!(
                err.contains(&format!("field {name}")),
                "{}: a changed {name} was not named: {err}",
                file.vectors[index].id
            );
            file.vectors[index]
                .fields
                .as_mut()
                .unwrap()
                .get_mut(&name)
                .unwrap()
                .replace_range(0..2, &original);
            swept += 1;
        }
    }
    assert_eq!(swept, 27 + 32, "fields swept");
    tacenta_vectors_rust::check_file(&file).expect("the restored vector passes");
}

/// Every input that shapes an output changes the run when it changes. The
/// byte changed is the sixth, clear of an X25519 secret's clamped first and
/// last bytes and inside the `d` half of an ML-KEM `d || z` draw. The one
/// input named below is consumed and cannot be observed: the repeated receive
/// takes no Diffie-Hellman step, so the fresh key it draws is never used.
#[test]
fn session_end_to_end_runner_depends_on_every_input() {
    const UNOBSERVABLE: &[&str] = &["bob_repeat_random"];
    let mut file = e2e_file();
    let mut swept = 0;
    for index in 0..file.vectors.len() {
        let names: Vec<String> = file.vectors[index].inputs.keys().cloned().collect();
        for name in names {
            let original = file.vectors[index].inputs[&name].clone();
            let mut changed = original.clone();
            let flipped = if &original[10..12] == "00" {
                "01"
            } else {
                "00"
            };
            changed.replace_range(10..12, flipped);
            file.vectors[index].inputs.insert(name.clone(), changed);
            let result = tacenta_vectors_rust::check_file(&file);
            file.vectors[index].inputs.insert(name.clone(), original);
            if UNOBSERVABLE.contains(&name.as_str()) {
                assert!(
                    result.is_ok(),
                    "{name} is documented as unobservable, yet changing it changed the run"
                );
            } else {
                assert!(
                    result.is_err(),
                    "{}: changing input {name} did not change the run",
                    file.vectors[index].id
                );
            }
            swept += 1;
        }
    }
    assert_eq!(swept, 17 + 16, "inputs swept");
}
