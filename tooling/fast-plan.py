#!/usr/bin/env python3
"""Choose which diff-scoped checks `tooling/fast.sh` runs, from a list of changed paths.

    python3 tooling/fast-plan.py [--root DIR] < paths      one repository-relative path per line
    python3 tooling/fast-plan.py [--root DIR] --paths-from FILE

It reads nothing but the paths and, to place a Rust file in a package, the Cargo manifests under
`--root` (default: the repository). It prints one line per decision, sorted, and runs nothing, so the
case runner can hold the selection to exact output. The lines:

    ci-fast                           always: `tooling/ci.sh --fast` runs whatever the diff
    rust ROOT ALL                     a Cargo.toml or Cargo.lock under ROOT changed, or the root is a single
                                      package: fmt, clippy and test the whole workspace
    rust ROOT PKG[,PKG...]            only the named packages of ROOT's workspace
    lean PROJECT FILE                 `lake env lean FILE` from PROJECT (FILE relative to PROJECT)
    lean-config PROJECT FILE          a lakefile, manifest or toolchain pin changed: only a full
                                      `lake build` shows what it did
    gate-inventory                    a file under tooling/ or .github/, or the generated inventory itself,
                                      changed: `tooling/gate-inventory.py --check`, which no step of `ci.sh`
                                      runs (hosted CI runs it in the checks job)
    deep                              a file under tooling/ or .github/, or regenerate-in-container.sh,
                                      changed: `ci.sh --fast` also runs its `deep_only` case runners (the
                                      workflow checker's, the container regeneration's and the assurance and
                                      evidence tooling's), as `--deep` asks
    covered AREA                      the checks for AREA (spec, workflows) are steps of `ci.sh --fast`,
                                      which always runs (the workflow checker's cases with `deep`, which a
                                      workflow change selects), so the diff adds nothing to run
    uncovered WORKSPACE N             N changed paths in a Cargo workspace no fast check reads (the fuzz
                                      workspaces, the vendored upstream patches, and a workspace's toolchain,
                                      clippy, rustfmt, deny or `.cargo` configuration); the run then ends
                                      "ok WITH UNCHECKED", never plain "ok"
    other N                           N changed paths in none of the above (documents, tooling): read by
                                      `ci.sh --fast` where a check names them, otherwise by nothing here

How a path is placed. A path is Rust when its nearest ancestor holding a `Cargo.toml` exists and the path
is not a Markdown file: the Cargo root is the nearest ancestor from there whose manifest has a
`[workspace]` table. A manifest or lockfile change makes the root `ALL`. Under a root, a path inside a
workspace member's directory selects that member's package, and a path in the root package's own
directories (`src`, `tests`, `examples`, `benches`, `build.rs`) selects the root package; a root that
has no members is `ALL` for any change. The fuzz workspaces and the vendored upstream patches are not
checked here.

What this does not do: select the packages that depend on a changed one. A change to a leaf crate is
formatted, linted and tested as that crate alone; the crates above it, and the vectors runner, are
checked by the full gate.
"""
import argparse
import functools
import os
import re
import sys

UNCOVERED_ROOTS = (re.compile(r"(^|/)fuzz$"), re.compile(r"^tacenta-proofs/upstream/"))
ROOT_PACKAGE_DIRS = ("src", "tests", "examples", "benches")
# Files that change how a workspace is built or linted without being a package's source: no fast check reads
# them, so a change to one is reported as unchecked rather than counted as `other`.
RUST_CONFIG = ("rust-toolchain", "rust-toolchain.toml", "clippy.toml", ".clippy.toml", "rustfmt.toml",
               ".rustfmt.toml", "deny.toml")
LEAN_PROJECTS = ("tacenta-proofs/translation", "tacenta-proofs", "tacenta-model")
LEAN_CONFIG = ("lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain")
WORKFLOW_PREFIXES = (".github/workflows/", ".github/actions/")
WORKFLOW_FILES = ("tooling/check-workflows.sh", "tooling/check-actionlint.sh", "tooling/required-steps.json",
                  "tooling/install-actionlint.sh")
INVENTORY_PREFIXES = ("tooling/", ".github/")
DEEP_PREFIXES = ("tooling/", ".github/")
DEEP_FILES = ("tacenta-proofs/scripts/regenerate-in-container.sh",)
INVENTORY_FILE = "tacenta-proofs/GATE-INVENTORY.md"
SPEC_PREFIXES = ("tacenta-spec/", "tacenta-test-vectors/vectors/", "tacenta-test-vectors/schema/",
                 "tacenta-test-vectors/traces/", "tacenta-test-vectors/runners/independent/")


@functools.lru_cache(maxsize=None)
def read(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as handle:
            return handle.read()
    except OSError:
        return ""


def manifest_has_workspace(text):
    return re.search(r"^\[workspace\]", text, re.M) is not None


def package_name(text):
    """The `name` of the manifest's [package] table, or None."""
    in_package = False
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("["):
            in_package = stripped == "[package]"
            continue
        if in_package:
            found = re.match(r'name\s*=\s*"([^"]+)"', stripped)
            if found:
                return found.group(1)
    return None


def members(text):
    """The `members` array of the manifest's [workspace] table (directory names), or []."""
    found = re.search(r"^\[workspace\].*?^members\s*=\s*\[(.*?)\]", text, re.M | re.S)
    if not found:
        return []
    body = re.sub(r"#[^\n]*", "", found.group(1))
    return re.findall(r'"([^"]+)"', body)


def cargo_dirs(rel):
    """The directories from the path's own directory up to the repository root, nearest first."""
    parts = rel.split("/")[:-1]
    return ["/".join(parts[:n]) for n in range(len(parts), -1, -1)]


def place(root, rel):
    """(workspace root dir, nearest package dir) for a path, or None when no Cargo.toml encloses it. A
    package that no [workspace] table encloses is its own workspace root."""
    package_dir = None
    for directory in cargo_dirs(rel):
        manifest = os.path.join(root, directory, "Cargo.toml")
        if not os.path.exists(manifest):
            continue
        if package_dir is None:
            package_dir = directory
        if manifest_has_workspace(read(manifest)):
            return directory, package_dir
    # A package that no [workspace] table encloses is its own workspace root.
    return (package_dir, package_dir) if package_dir is not None else None


def rust_selection(root, rel, rust):
    """Record in `rust` ({workspace: "ALL" or set of packages}) what a changed path selects. Returns
    ("uncovered", workspace) for a path in an unchecked workspace, ("other", None) when it selects nothing,
    else None."""
    placed = place(root, rel)
    if placed is None:
        return ("other", None)
    workspace, _ = placed
    if any(pattern.search(workspace) for pattern in UNCOVERED_ROOTS):
        return ("uncovered", workspace)
    if rust.get(workspace) == "ALL":
        return None
    manifest_text = read(os.path.join(root, workspace, "Cargo.toml"))
    member_dirs = members(manifest_text)
    if os.path.basename(rel) in ("Cargo.toml", "Cargo.lock") or not member_dirs:
        rust[workspace] = "ALL"
        return None
    inside = rel[len(workspace) + 1:] if workspace else rel
    if os.path.basename(rel) in RUST_CONFIG or ("/" + inside).count("/.cargo/"):
        return ("uncovered", workspace)
    first = inside.split("/")[0]
    if first in member_dirs:
        name = package_name(read(os.path.join(root, workspace, first, "Cargo.toml")))
    elif first in ROOT_PACKAGE_DIRS or first == "build.rs":
        name = package_name(manifest_text)
    else:
        name = None
    if name is None:
        return ("other", None)
    rust.setdefault(workspace, set()).add(name)
    return None


def plan(root, paths):
    lines = {"ci-fast"}
    rust = {}  # workspace root -> "ALL" or a set of package names
    other = 0
    uncovered = {}
    for rel in sorted(set(paths)):
        base = os.path.basename(rel)
        if rel.startswith(WORKFLOW_PREFIXES) or rel in WORKFLOW_FILES:
            lines.add("covered workflows")
            continue
        project = next((p for p in LEAN_PROJECTS if rel.startswith(p + "/")), None)
        if project is not None and (rel.endswith(".lean") or base in LEAN_CONFIG):
            inside = rel[len(project) + 1:]
            kind = "lean-config" if inside in LEAN_CONFIG else "lean"
            lines.add(f"{kind} {project} {inside}")
            continue
        if not rel.endswith(".md"):
            verdict = rust_selection(root, rel, rust)
            if verdict is None:
                continue
            if verdict[0] == "uncovered":
                uncovered[verdict[1]] = uncovered.get(verdict[1], 0) + 1
                continue
        if rel.startswith(SPEC_PREFIXES):
            lines.add("covered spec")
            continue
        other += 1
    if any(rel.startswith(INVENTORY_PREFIXES) or rel == INVENTORY_FILE for rel in paths):
        lines.add("gate-inventory")
    if any(rel.startswith(DEEP_PREFIXES) or rel in DEEP_FILES for rel in paths):
        lines.add("deep")
    for workspace, selected in sorted(rust.items()):
        names = "ALL" if selected == "ALL" else ",".join(sorted(selected))
        lines.add(f"rust {workspace or '.'} {names}")
    for workspace, count in sorted(uncovered.items()):
        lines.add(f"uncovered {workspace} {count}")
    if other:
        lines.add(f"other {other}")
    return sorted(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    parser.add_argument("--paths-from", metavar="FILE", help="read the paths from FILE (default: standard input)")
    args = parser.parse_args()
    if args.paths_from:
        text = read(args.paths_from)
    else:
        text = sys.stdin.read()
    paths = [line.strip() for line in text.splitlines() if line.strip()]
    for line in plan(os.path.abspath(args.root), paths):
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
