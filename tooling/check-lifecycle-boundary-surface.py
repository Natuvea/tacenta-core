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

# These adapters and the five Session roots are intentionally written as direct
# matches. Leaving borrowed Option adapters in Rust makes Aeneas turn otherwise
# pure control flow into extra opaque assumptions.
HEADER_ADAPTER_ROOTS = {"lifecycle.composite_of", "lifecycle.msg_of"}
FORBIDDEN_OPTION_OPERATIONS = {
    "core.option.Option.as_ref",
    "core.option.Option.as_deref",
    "core.option.Option.map",
    "core.option.Option.map_or",
    "core.option.Option.ok_or",
    "core.result.Result.map_err",
}

# The thirteen boundary operations reachable from the five Session proof
# roots, grouped as tacenta-model/SESSION-L4-PRIMITIVE-BOUNDARY-DECISION.md
# names them: DhCodecTotal (the six dh.* codec items), DhAgreeTotal (agree),
# AeadSealTotal/AeadOpenTotal (aead.encrypt/decrypt), KemEncapsulateTotal,
# KemDecapsulateTotal, KemCiphertextLenTotal, XeddsaVerifyTotal. Signing is
# XeddsaSignTotal, reachable from publication rather than from a root, and
# Random32Total has no boundary name (the RngCore trait dictionary carries it),
# so neither appears in this set. The mapping is recorded in
# tacenta-model/SESSION-L4-PHASE0-SPIKE-20260918.md.
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
        proof_surface = reachable_declarations(
            parsed, SESSION_ROOTS | HEADER_ADAPTER_ROOTS
        )
    except (OSError, ValueError) as error:
        print(f"lifecycle-boundary-surface: {error}", file=sys.stderr)
        return 1

    errors = check_set("Session roots", session, EXPECTED_SESSION_OPERATIONS)
    errors += check_set("signing root", signing, EXPECTED_SIGNING_OPERATIONS)
    opaque_options = proof_surface & FORBIDDEN_OPTION_OPERATIONS
    if opaque_options:
        errors.append(
            "Session proof surface regained opaque standard operation(s): "
            + ", ".join(sorted(opaque_options))
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
