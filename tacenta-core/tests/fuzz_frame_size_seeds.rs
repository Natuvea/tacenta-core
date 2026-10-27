//! The `frame_size_boundary` fuzz target's seed corpus, run through the target's own entry
//! (`fuzz/frame_size_entry.rs`) by an ordinary test, so that what the seeds exercise is checked on every
//! `cargo test`, whether or not libFuzzer is installed. **Tested only; this is not a proof, and it is not the
//! fuzz campaign** (`fuzz/README.md`, The size rule's boundary campaign, says how to run that).
//!
//! Raising a fuzz target's `-max_len` does not show that the large inputs reach anything. This does, from the
//! outputs alone: for every committed seed it requires the branch `fuzz/frame_size_seeds.txt` names, on
//! `Session::decrypt` and on `establish_responder`, and it requires each branch of the size rule to be taken
//! at least once on each entry: refused by the outer bound, by the nested bound, by the ratchet bound, admitted
//! at exactly a bound and passed on to the decoder, and refused under the bounds as another decode failure.
//! The entry itself asserts, for every seed, that the library's verdict agrees with the rule computed in the
//! harness and that a size refusal draws nothing and changes nothing.

use std::collections::BTreeSet;
use std::path::Path;

#[allow(
    dead_code,
    reason = "the fuzz target uses the rest of the entry module"
)]
#[path = "../fuzz/frame_size_entry.rs"]
mod frame_size_entry;

use frame_size_entry::{Branch, CAP, frame_of, run};
use tacenta_core::serialization::MAX_INITIAL_FRAME_LEN;

const BRANCHES: [Branch; 5] = [
    Branch::OuterTooLong,
    Branch::NestedTooLong,
    Branch::RatchetTooLong,
    Branch::AtLimitToDecoder,
    Branch::WithinBoundsMalformed,
];

fn branch(name: &str) -> Branch {
    *BRANCHES
        .iter()
        .chain([Branch::Other].iter())
        .find(|b| b.name() == name)
        .unwrap_or_else(|| panic!("unknown branch {name}"))
}

#[test]
fn the_boundary_seeds_take_every_branch_of_the_size_rule() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("fuzz");
    let manifest =
        std::fs::read_to_string(root.join("frame_size_seeds.txt")).expect("read the seed manifest");
    let corpus = root.join("corpus/frame_size_boundary");

    let mut session_hits = BTreeSet::new();
    let mut responder_hits = BTreeSet::new();
    let mut longest = 0usize;
    let mut seeds = 0;
    for line in manifest
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
    {
        let parts: Vec<&str> = line.split_whitespace().collect();
        assert_eq!(parts.len(), 3, "manifest line {line:?}");
        let data = std::fs::read(corpus.join(parts[0]))
            .unwrap_or_else(|e| panic!("seed {} is missing: {e}", parts[0]));
        let frame = frame_of(&data).expect("every seed describes a frame");
        longest = longest.max(frame.len());
        let report = run(&data).expect("every seed describes a frame");
        assert_eq!(
            (report.session.name(), report.responder.name()),
            (parts[1], parts[2]),
            "seed {}: the branches decrypt and establish_responder took",
            parts[0]
        );
        assert_eq!(report.session, branch(parts[1]));
        session_hits.insert(report.session);
        responder_hits.insert(report.responder);
        seeds += 1;
    }
    assert!(seeds >= 30, "only {seeds} seeds in the manifest");
    for b in BRANCHES {
        assert!(
            session_hits.contains(&b),
            "no seed takes {} on decrypt",
            b.name()
        );
        assert!(
            responder_hits.contains(&b),
            "no seed takes {} on establish_responder",
            b.name()
        );
    }
    assert!(
        longest > MAX_INITIAL_FRAME_LEN,
        "the seeds reach {longest} bytes, not past MAX_INITIAL_FRAME_LEN"
    );
    // The target's frames reach past one padding block over the outer bound, at compile time.
    const _: () = assert!(CAP > MAX_INITIAL_FRAME_LEN + 16);

    // Files the fuzzer has added since: each must still run without a finding.
    let listed: BTreeSet<String> = manifest
        .lines()
        .filter(|l| !l.starts_with('#'))
        .filter_map(|l| l.split_whitespace().next().map(str::to_string))
        .collect();
    for entry in std::fs::read_dir(&corpus).expect("read the corpus") {
        let path = entry.expect("a corpus entry").path();
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_string();
        if !listed.contains(&name) {
            let _ = run(&std::fs::read(&path).expect("read a corpus file"));
        }
    }
}
