//! The vendored NIST ACVP ML-KEM sample vectors are the files the provenance
//! record names, and the derived fixture is a re-arrangement of them.
//!
//! `tests/data/acvp-ml-kem/` holds upstream's JSON files byte for byte (from
//! the `usnistgov/ACVP-Server` repository at the commit named in
//! `PROVENANCE.md`), a fixture of the ML-KEM-1024 cases joined into one file,
//! and the script that wrote it. `kem_acvp_vectors.rs` tests against the
//! fixture. This file is what stops the fixture drifting from upstream:
//!
//! 1. `SHA256SUMS.txt` is the one file whose hash is written down here (below),
//!    so an edit to the list is an edit to this file too.
//! 2. Every vendored file hashes to its line of `SHA256SUMS.txt`, the set of
//!    files on disk is exactly the set the list and this test name, and no
//!    other file is present.
//! 3. Re-running the extraction, in Rust here, over the vendored originals
//!    reproduces the fixture byte for byte. The Rust version follows the
//!    procedure of `extract.py`, which is vendored beside the data and is the
//!    procedure `PROVENANCE.md` records; a value in the fixture changed by
//!    hand, a case deleted, or an original changed, fails one of these.
//!
//! Nothing is computed from the implementation under test, and there is no
//! mode that rewrites a hash or the fixture. To update the data, replace the
//! originals with a new upstream commit's files, re-run the script, and change
//! the hash below by hand in a reviewed change.
//!
//! This establishes that the vendored files are the ones recorded. It does not
//! establish that upstream's expected values are right, which is the premise
//! of using them.

use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

const DATA: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/acvp-ml-kem");

/// SHA-256 of `SHA256SUMS.txt`. Written here so that editing the list of
/// hashes is not enough to change what the test accepts.
const SUMS_SHA256: &str = "cbaf526d3f28e340a78c055191c203c27eb6226155d6bdab0994cd38d8c7afb9";

/// Every file the sums list must name, and nothing else.
const LISTED: [&str; 19] = [
    "original/ML-KEM-encapDecap-FIPS203-tr1/expectedResults.json",
    "original/ML-KEM-encapDecap-FIPS203-tr1/internalProjection.json",
    "original/ML-KEM-encapDecap-FIPS203-tr1/prompt.json",
    "original/ML-KEM-encapDecap-FIPS203-tr1/registration.json",
    "original/ML-KEM-encapDecap-FIPS203-tr1/validation.json",
    "original/ML-KEM-encapDecap-FIPS203/expectedResults.json",
    "original/ML-KEM-encapDecap-FIPS203/internalProjection.json",
    "original/ML-KEM-encapDecap-FIPS203/prompt.json",
    "original/ML-KEM-encapDecap-FIPS203/registration.json",
    "original/ML-KEM-encapDecap-FIPS203/validation.json",
    "original/ML-KEM-keyGen-FIPS203/expectedResults.json",
    "original/ML-KEM-keyGen-FIPS203/internalProjection.json",
    "original/ML-KEM-keyGen-FIPS203/prompt.json",
    "original/ML-KEM-keyGen-FIPS203/registration.json",
    "original/ML-KEM-keyGen-FIPS203/validation.json",
    "original/repo-root/README.md",
    "extract.py",
    "mlkem1024-acvp-fixture.json",
    "PROVENANCE.md",
];

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

fn read(rel: &str) -> Vec<u8> {
    std::fs::read(Path::new(DATA).join(rel)).unwrap_or_else(|e| panic!("cannot read {rel}: {e}"))
}

fn walk(dir: &Path, root: &Path, out: &mut BTreeSet<String>) {
    for entry in std::fs::read_dir(dir).expect("read_dir") {
        let path: PathBuf = entry.expect("entry").path();
        if path.is_dir() {
            walk(&path, root, out);
        } else {
            let rel = path.strip_prefix(root).expect("prefix");
            out.insert(rel.to_str().expect("utf-8 path").replace('\\', "/"));
        }
    }
}

/// `SHA256SUMS.txt` as (hash, path) pairs.
fn sums() -> Vec<(String, String)> {
    let text = String::from_utf8(read("SHA256SUMS.txt")).expect("utf-8");
    text.lines()
        .map(|l| {
            let (h, p) = l
                .split_once("  ")
                .unwrap_or_else(|| panic!("bad line {l:?}"));
            (h.to_string(), p.to_string())
        })
        .collect()
}

#[test]
fn the_list_of_hashes_is_the_one_this_file_names() {
    assert_eq!(
        sha256_hex(&read("SHA256SUMS.txt")),
        SUMS_SHA256,
        "SHA256SUMS.txt changed"
    );
}

#[test]
fn the_files_on_disk_are_exactly_the_files_recorded() {
    let mut on_disk = BTreeSet::new();
    walk(Path::new(DATA), Path::new(DATA), &mut on_disk);
    let mut want: BTreeSet<String> = LISTED.iter().map(|s| s.to_string()).collect();
    want.insert("SHA256SUMS.txt".to_string());
    assert_eq!(on_disk, want, "vendored file set differs from the record");
}

#[test]
fn every_vendored_file_hashes_to_its_recorded_value() {
    let sums = sums();
    // PROVENANCE.md carries prose and is not hashed: it cannot contain its own
    // hash, and the fixture's correctness does not rest on it.
    let want: BTreeSet<&str> = LISTED
        .iter()
        .copied()
        .filter(|p| *p != "PROVENANCE.md")
        .collect();
    let got: BTreeSet<&str> = sums.iter().map(|(_, p)| p.as_str()).collect();
    assert_eq!(got, want, "SHA256SUMS.txt names the wrong files");
    assert_eq!(sums.len(), want.len(), "a path is listed twice");
    for (hash, path) in &sums {
        assert_eq!(
            &sha256_hex(&read(path)),
            hash,
            "{path} differs from its recorded hash"
        );
    }
}

// ---------------------------------------------------------------------------
// Re-running the extraction
// ---------------------------------------------------------------------------

fn die(msg: String) -> ! {
    panic!("extraction failed: {msg}")
}

fn load(dir: &str, name: &str) -> Value {
    let bytes = read(&format!("original/{dir}/{name}.json"));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| die(format!("{dir}/{name}: {e}")))
}

fn arr<'a>(v: &'a Value, key: &str) -> &'a Vec<Value> {
    v[key]
        .as_array()
        .unwrap_or_else(|| die(format!("no array {key}")))
}

fn key_len(k: &str) -> Option<usize> {
    match k {
        "d" | "z" | "m" | "k" => Some(32),
        "ek" => Some(1568),
        "dk" => Some(3168),
        "c" => Some(1568),
        _ => None,
    }
}

/// The output fields of each mode, as in `extract.py`.
fn out_fields(mode_fn: &str) -> &'static [&'static str] {
    match mode_fn {
        "keyGen" => &["dk", "ek"],
        "encapsulation" => &["c", "k"],
        "decapsulation" => &["k"],
        "encapsulationKeyCheck" | "decapsulationKeyCheck" => &["testPassed"],
        _ => die(format!("mode {mode_fn}")),
    }
}

/// directory -> selected (function, keyFormat) pairs, as `SEL` in `extract.py`.
fn selection(dir: &str) -> Vec<(Option<&'static str>, Option<&'static str>)> {
    match dir {
        "ML-KEM-keyGen-FIPS203" => vec![(None, None)],
        "ML-KEM-encapDecap-FIPS203" => vec![
            (Some("encapsulation"), None),
            (Some("decapsulation"), None),
            (Some("encapsulationKeyCheck"), None),
            (Some("decapsulationKeyCheck"), None),
        ],
        "ML-KEM-encapDecap-FIPS203-tr1" => vec![
            (Some("encapsulation"), None),
            (Some("decapsulation"), Some("seed")),
            (Some("decapsulation"), Some("expanded")),
            (Some("encapsulationKeyCheck"), None),
            (Some("decapsulationKeyCheck"), Some("expanded")),
        ],
        _ => die(format!("directory {dir}")),
    }
}

fn obj_without(v: &Value, skip: &str) -> serde_json::Map<String, Value> {
    v.as_object()
        .unwrap_or_else(|| die("not an object".into()))
        .iter()
        .filter(|(k, _)| k.as_str() != skip)
        .map(|(k, x)| (k.clone(), x.clone()))
        .collect()
}

fn extract_dir(dir: &str) -> Value {
    let (pr, ex, ip) = (
        load(dir, "prompt"),
        load(dir, "expectedResults"),
        load(dir, "internalProjection"),
    );
    for a in [&pr, &ex, &ip] {
        if a["algorithm"] != "ML-KEM" || a["revision"] != pr["revision"] || a["mode"] != pr["mode"]
        {
            die(format!("{dir} header mismatch"));
        }
    }
    let find = |groups: &Vec<Value>, tg: &Value| -> Value {
        let mut hits = groups.iter().filter(|g| g["tgId"] == *tg);
        let g = hits
            .next()
            .unwrap_or_else(|| die(format!("group {tg} missing in expected/internal")));
        if hits.next().is_some() {
            die(format!("group {tg} duplicated"));
        }
        g.clone()
    };
    let wanted = selection(dir);
    let mut seen: BTreeSet<(Option<String>, Option<String>)> = BTreeSet::new();
    let mut groups = Vec::new();
    for g in arr(&pr, "testGroups") {
        if g["parameterSet"] != "ML-KEM-1024" {
            continue;
        }
        let fnn = g.get("function").and_then(|v| v.as_str());
        let kf = g.get("keyFormat").and_then(|v| v.as_str());
        if !wanted.iter().any(|(f, k)| *f == fnn && *k == kf) {
            die(format!(
                "{dir} unexpected group {fnn:?}/{kf:?} tg{}",
                g["tgId"]
            ));
        }
        seen.insert((fnn.map(String::from), kf.map(String::from)));
        let mode_fn = fnn.unwrap_or("keyGen");
        let tests = arr(g, "tests");
        if tests.is_empty() {
            die(format!("empty group {}", g["tgId"]));
        }
        let e = find(arr(&ex, "testGroups"), &g["tgId"]);
        let i = find(arr(&ip, "testGroups"), &g["tgId"]);
        let (et, it) = (arr(&e, "tests"), arr(&i, "tests"));
        if et.len() != tests.len() || it.len() != tests.len() {
            die(format!("case count mismatch tg{}", g["tgId"]));
        }
        let by_tc = |list: &Vec<Value>, tc: &Value| -> Value {
            let mut hits = list.iter().filter(|t| t["tcId"] == *tc);
            let t = hits
                .next()
                .unwrap_or_else(|| die(format!("case {tc} lacks expected answer")));
            if hits.next().is_some() {
                die(format!("case {tc} duplicated"));
            }
            t.clone()
        };
        let mut cases = Vec::new();
        for t in tests {
            let tc = &t["tcId"];
            let (etc, itc) = (by_tc(et, tc), by_tc(it, tc));
            let inputs = obj_without(t, "tcId");
            let outputs = obj_without(&etc, "tcId");
            let mut got: Vec<&str> = outputs.keys().map(String::as_str).collect();
            got.sort_unstable();
            if got != out_fields(mode_fn) {
                die(format!("tc{tc} output fields {got:?}"));
            }
            for (k, v) in inputs.iter().chain(outputs.iter()) {
                if let Some(n) = key_len(k) {
                    if v.as_str().map(str::len) != Some(2 * n) {
                        die(format!("tc{tc} {k} length"));
                    }
                }
                if itc.get(k) != Some(v) {
                    die(format!("tc{tc} {k} differs in internalProjection"));
                }
            }
            let mut c = serde_json::Map::new();
            c.insert("tcId".into(), tc.clone());
            c.insert("inputs".into(), Value::Object(inputs));
            c.insert("expected".into(), Value::Object(outputs));
            if let Some(r) = itc.get("reason") {
                c.insert("reason".into(), r.clone());
            }
            cases.push(Value::Object(c));
        }
        let mut grp = serde_json::Map::new();
        grp.insert("tgId".into(), g["tgId"].clone());
        grp.insert("testType".into(), g["testType"].clone());
        grp.insert("parameterSet".into(), "ML-KEM-1024".into());
        grp.insert("cases".into(), Value::Array(cases));
        if let Some(f) = fnn {
            grp.insert("function".into(), f.into());
        }
        if let Some(k) = kf {
            grp.insert("keyFormat".into(), k.into());
        }
        groups.push(Value::Object(grp));
    }
    let want: BTreeSet<(Option<String>, Option<String>)> = wanted
        .iter()
        .map(|(f, k)| (f.map(String::from), k.map(String::from)))
        .collect();
    if seen != want {
        die(format!("{dir} missing groups"));
    }
    let mut rev = serde_json::Map::new();
    for k in ["algorithm", "mode", "revision"] {
        rev.insert(k.into(), pr[k].clone());
    }
    rev.insert("groups".into(), Value::Array(groups));
    Value::Object(rev)
}

/// Canonical JSON as Python's `json.dump(sort_keys=True, separators=(",",":"))`
/// writes it for these values (ASCII strings, integers, booleans).
fn canonical(v: &Value, out: &mut String) {
    match v {
        Value::Null => out.push_str("null"),
        Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Value::Number(n) => out.push_str(&n.to_string()),
        Value::String(s) => {
            assert!(s.is_ascii(), "non-ASCII string in the vectors");
            out.push_str(&serde_json::to_string(s).expect("string"));
        }
        Value::Array(a) => {
            out.push('[');
            for (i, x) in a.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                canonical(x, out);
            }
            out.push(']');
        }
        Value::Object(m) => {
            let mut keys: Vec<&String> = m.keys().collect();
            keys.sort();
            out.push('{');
            for (i, k) in keys.into_iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&serde_json::to_string(k).expect("key"));
                out.push(':');
                canonical(&m[k], out);
            }
            out.push('}');
        }
    }
}

/// Re-running the extraction over the vendored originals writes the vendored
/// fixture, byte for byte.
#[test]
fn the_fixture_is_reproduced_from_the_vendored_originals() {
    let mut revisions = serde_json::Map::new();
    for dir in [
        "ML-KEM-encapDecap-FIPS203",
        "ML-KEM-encapDecap-FIPS203-tr1",
        "ML-KEM-keyGen-FIPS203",
    ] {
        revisions.insert(dir.into(), extract_dir(dir));
    }
    let mut top = serde_json::Map::new();
    top.insert(
        "source".into(),
        "usnistgov/ACVP-Server gen-val/json-files (see PROVENANCE.md)".into(),
    );
    top.insert("revisions".into(), Value::Object(revisions));
    let mut text = String::new();
    canonical(&Value::Object(top), &mut text);
    text.push('\n');
    let vendored = read("mlkem1024-acvp-fixture.json");
    assert_eq!(
        text.len(),
        vendored.len(),
        "re-extracted fixture and vendored fixture differ in length"
    );
    if text.as_bytes() != vendored.as_slice() {
        let at = text
            .bytes()
            .zip(vendored.iter())
            .position(|(a, b)| a != *b)
            .unwrap_or(0);
        panic!("re-extracted fixture differs from the vendored one at byte {at}");
    }
}
