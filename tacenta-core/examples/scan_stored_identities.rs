//! Scan stored sessions and prekey stores for identity keys this release refuses.
//!
//! Run before rolling out a release that refuses a stored session or prekey
//! store whose identity key is not an identity key
//! (session-persistence.md, Stored curve public keys):
//!
//! ```text
//! cargo run --example scan_stored_identities -- session FILE...
//! cargo run --example scan_stored_identities -- prekey-store FILE...
//! ```
//!
//! Each argument after the kind is a file holding one exported session
//! (`Session::export`) or one stored prekey store (`PrekeyStore::to_bytes`), or a
//! directory whose files are read the same way. One line is printed per file:
//! `ok`, `refused` with the keys the release refuses, or `unreadable` with the
//! reason the bytes do not decode.
//!
//! The exit status is 0 when every file is `ok`, 1 when any file is `refused`,
//! and 2 when any file is unreadable and none is refused.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use tacenta_core::sessions::{
    StoredSessionIdentities, scan_stored_prekey_identity, scan_stored_session_identities,
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Session,
    PrekeyStore,
}

fn files_under(path: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if path.is_dir() {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(path)?
            .map(|entry| entry.map(|e| e.path()))
            .collect::<Result<_, _>>()?;
        entries.sort();
        for entry in entries {
            if entry.is_file() {
                out.push(entry);
            }
        }
    } else {
        out.push(path.to_path_buf());
    }
    Ok(())
}

/// The verdict for one file: whether it is refused, and the line to print.
fn scan(kind: Kind, bytes: &[u8]) -> (Verdict, String) {
    match kind {
        Kind::Session => match scan_stored_session_identities(bytes) {
            Ok(StoredSessionIdentities {
                ours: true,
                peer: true,
            }) => (Verdict::Ok, "ok".to_string()),
            Ok(found) => {
                let mut refused = Vec::new();
                if !found.ours {
                    refused.push("our identity");
                }
                if !found.peer {
                    refused.push("peer identity");
                }
                (
                    Verdict::Refused,
                    format!("refused: {}", refused.join(" and ")),
                )
            }
            Err(reason) => (Verdict::Unreadable, format!("unreadable: {reason:?}")),
        },
        Kind::PrekeyStore => match scan_stored_prekey_identity(bytes) {
            Ok(true) => (Verdict::Ok, "ok".to_string()),
            Ok(false) => (Verdict::Refused, "refused: identity key".to_string()),
            Err(reason) => (Verdict::Unreadable, format!("unreadable: {reason:?}")),
        },
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Ok,
    Refused,
    Unreadable,
}

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let kind = match args.next().as_deref() {
        Some("session") => Kind::Session,
        Some("prekey-store") => Kind::PrekeyStore,
        _ => {
            eprintln!(
                "usage: scan_stored_identities (session | prekey-store) FILE_OR_DIRECTORY..."
            );
            return ExitCode::from(64);
        }
    };
    let mut paths = Vec::new();
    for argument in args {
        if let Err(error) = files_under(Path::new(&argument), &mut paths) {
            eprintln!("{argument}: {error}");
            return ExitCode::from(66);
        }
    }
    if paths.is_empty() {
        eprintln!("no files to scan");
        return ExitCode::from(64);
    }
    let (mut refused, mut unreadable) = (0usize, 0usize);
    for path in &paths {
        let (verdict, line) = match std::fs::read(path) {
            Ok(bytes) => scan(kind, &bytes),
            Err(error) => (Verdict::Unreadable, format!("unreadable: {error}")),
        };
        match verdict {
            Verdict::Ok => {}
            Verdict::Refused => refused += 1,
            Verdict::Unreadable => unreadable += 1,
        }
        println!("{}: {line}", path.display());
    }
    println!(
        "{} scanned, {} refused, {} unreadable",
        paths.len(),
        refused,
        unreadable
    );
    if refused > 0 {
        ExitCode::from(1)
    } else if unreadable > 0 {
        ExitCode::from(2)
    } else {
        ExitCode::SUCCESS
    }
}
