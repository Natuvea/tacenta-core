#!/usr/bin/env python3
"""Pin the opaque primitive calls reachable from the Session proof surface.

This is a deliberately small source-level check over the committed Aeneas
translation.  It is not a substitute for rebuilding that translation.  Its
job is to make a changed opaque-call surface visible: a new reachable boundary
operation must be assigned to a reviewed contract before this check can pass.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


DEFAULT_TRANSLATION = Path(
    "tacenta-proofs/translation/Translation/TacentaLifecycle.lean"
)

SESSION_ROOTS = {
    "lifecycle.Session.encrypt",
    "lifecycle.Session.decrypt",
    "lifecycle.establish_initiator",
    "lifecycle.establish_responder",
    "lifecycle.Session.import",
}

# Signing is outside the five Session theorem roots, but the lifecycle leaf
# contains the publication methods that use it.  The boundary decision counts
# that operation, so keep its translated call visible too.
SIGNING_ROOTS = {"lifecycle.Identity.sign_message"}

# These two adapters are intentionally written as direct matches.  Leaving the
# borrowed `Option::as_ref/map` chain in Rust makes Aeneas turn otherwise pure
# conversion code into two extra opaque assumptions.
HEADER_ADAPTER_ROOTS = {"lifecycle.composite_of", "lifecycle.msg_of"}
FORBIDDEN_HEADER_ADAPTER_OPERATIONS = {
    "core.option.Option.as_ref",
    "core.option.Option.map",
}

EXPECTED_SESSION_OPERATIONS = {
    "tacenta_boundary.aead.decrypt",
    "tacenta_boundary.aead.encrypt",
    "tacenta_boundary.dh.PrivateKey.agree",
    "tacenta_boundary.dh.PrivateKey.from_bytes",
    "tacenta_boundary.dh.PrivateKey.public_key",
    "tacenta_boundary.dh.PrivateKey.to_bytes",
    "tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq",
    "tacenta_boundary.dh.PublicKeyBytes.as_bytes",
    "tacenta_boundary.dh.PublicKeyBytes.from_bytes",
    "tacenta_boundary.kem.ciphertext_len",
    "tacenta_boundary.kem.decapsulate",
    "tacenta_boundary.kem.encapsulate",
    "tacenta_boundary.xeddsa.verify",
}

EXPECTED_SIGNING_OPERATIONS = {"tacenta_boundary.xeddsa.sign"}

DECLARATION = re.compile(
    r"(?m)^(def|impl_def|axiom|opaque|theorem|inductive|structure)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT = re.compile(r"--[^\n]*")


@dataclass(frozen=True)
class Declaration:
    body: str
    is_boundary_operation: bool


def without_comments(text: str) -> str:
    # Generated files do not nest block comments.  Removing documentation and
    # line comments prevents a prose mention from becoming evidence of a call.
    return LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))


def declarations(text: str) -> dict[str, Declaration]:
    matches = list(DECLARATION.finditer(text))
    result: dict[str, Declaration] = {}
    for index, match in enumerate(matches):
        kind = match.group(1)
        name = match.group(2)
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        body = without_comments(text[match.start() : end])
        header = body.split(":=", 1)[0].strip()
        # Boundary data types are opaque axioms too.  An operation is an axiom
        # whose declaration is not merely `name : Type`.
        is_type_axiom = kind == "axiom" and bool(
            re.match(
                r"axiom\s+" + re.escape(name) + r"\s*:\s*Type(?:\s|$)", header
            )
        )
        is_boundary_operation = (
            name.startswith("tacenta_boundary.")
            and kind == "axiom"
            and not is_type_axiom
        )
        result[name] = Declaration(body=body, is_boundary_operation=is_boundary_operation)
    return result


def reachable_declarations(
    parsed: dict[str, Declaration], roots: set[str]
) -> set[str]:
    missing_roots = roots - parsed.keys()
    if missing_roots:
        raise ValueError("missing proof root(s): " + ", ".join(sorted(missing_roots)))

    seen: set[str] = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        declaration = parsed[name]
        for token in TOKEN.findall(declaration.body):
            if token in parsed and token not in seen:
                pending.append(token)
    return seen


def reachable_operations(
    parsed: dict[str, Declaration], roots: set[str]
) -> set[str]:
    return {
        name
        for name in reachable_declarations(parsed, roots)
        if parsed[name].is_boundary_operation
    }


def check_set(label: str, actual: set[str], expected: set[str]) -> list[str]:
    errors: list[str] = []
    missing = expected - actual
    unexpected = actual - expected
    if missing:
        errors.append(f"{label}: expected operation(s) no longer reachable: " + ", ".join(sorted(missing)))
    if unexpected:
        errors.append(f"{label}: unclassified reachable operation(s): " + ", ".join(sorted(unexpected)))
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--translation", type=Path, default=DEFAULT_TRANSLATION)
    args = parser.parse_args()

    try:
        parsed = declarations(args.translation.read_text())
        session = reachable_operations(parsed, SESSION_ROOTS)
        signing = reachable_operations(parsed, SIGNING_ROOTS)
        header_adapters = reachable_declarations(parsed, HEADER_ADAPTER_ROOTS)
    except (OSError, ValueError) as error:
        print(f"lifecycle-boundary-surface: {error}", file=sys.stderr)
        return 1

    errors = check_set("Session roots", session, EXPECTED_SESSION_OPERATIONS)
    errors += check_set("signing root", signing, EXPECTED_SIGNING_OPERATIONS)
    opaque_header_adapters = header_adapters & FORBIDDEN_HEADER_ADAPTER_OPERATIONS
    if opaque_header_adapters:
        errors.append(
            "header adapters regained opaque Option operation(s): "
            + ", ".join(sorted(opaque_header_adapters))
        )
    if errors:
        for error in errors:
            print(f"lifecycle-boundary-surface: {error}", file=sys.stderr)
        return 1

    print(
        "lifecycle-boundary-surface: "
        f"{len(session)} Session operations and {len(signing)} signing operation classified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
