#!/usr/bin/env python3
"""List the claims ledger's sections for a review, write a receipt template, or show what changed.

    ledger-review-sections.py --pack PACK
    ledger-review-sections.py --pack PACK --template RECEIPT.json
    ledger-review-sections.py --pack PACK --since EARLIER

`--pack` is a verified evidence pack; its copy of `CLAIMS.md` is the one the
review is about. Without more it prints each section with its digest.

`--template` writes a receipt (schema 2) with the candidate, the pack binding and
every section's reference and digest filled in and everything the reviewer
decides left as a `REPLACE_WITH_...` placeholder, which
`check-ledger-review-receipt.py` refuses. It never chooses a disposition.

`--since EARLIER` compares with an earlier candidate: EARLIER is an earlier pack
(a directory), an earlier review receipt (schema 2, a `.json` file) or an earlier
`CLAIMS.md`. Each section is reported `unchanged`, `changed` or `new`, with the
earlier sections that are gone. This says which sections a re-review has to read
again if carrying an unchanged section's disposition forward is acceptable. It
does not say that it is, and nothing here records that a reviewer relied on it:
the reviewer states that basis in the receipt.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
_spec = importlib.util.spec_from_file_location("tacenta_review_checker", ROOT / "tooling/check-ledger-review-receipt.py")
checker = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(checker)


def earlier_sections(path: Path) -> dict[str, str]:
    if path.is_dir():
        return checker.claim_sections((path / checker.CLAIMS_IN_PACK).read_text())
    if path.suffix == ".json":
        receipt = checker.load(path, "earlier review receipt")
        if receipt.get("schema_version") != checker.SCHEMA_VERSION:
            checker.fail("the earlier receipt is not schema 2 and records no section digests; give its pack or its CLAIMS.md")
        return {c["reference"]: c["section_sha256"] for c in receipt.get("claims", [])}
    return checker.claim_sections(path.read_text())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--template", type=Path)
    parser.add_argument("--since", type=Path)
    args = parser.parse_args()
    try:
        if args.template and args.since:
            checker.fail("--template and --since cannot be combined")
        pack_manifest = checker.load(args.pack / "PACK-MANIFEST.json", "pack manifest")
        sections = checker.pack_sections(args.pack, pack_manifest)
        if args.template:
            if args.template.exists():
                checker.fail(f"refusing to replace {args.template}")
            template = {
                "schema_version": checker.SCHEMA_VERSION,
                "candidate": pack_manifest["candidate"],
                "evidence_pack": {"manifest_sha256": checker.digest(args.pack / "PACK-MANIFEST.json")},
                "reviewer": {"identity": "REPLACE_WITH_REVIEWER_IDENTITY",
                             "independence_statement": "REPLACE_WITH_AN_ACCURATE_INDEPENDENCE_STATEMENT"},
                "artifacts_read": ["REPLACE_WITH_THE_COMPLETE_ARTIFACT_LIST"],
                "claims": [{"reference": title, "disposition": "REPLACE_WITH_ACCEPTED_ACCEPTED_WITH_LIMIT_OR_FINDING",
                            "finding": "REPLACE_WITH_THE_SECTION_FINDING", "section_sha256": section_digest}
                           for title, section_digest in sections.items()],
            }
            args.template.write_text(json.dumps(template, indent=2) + "\n")
            print(f"ledger review sections: wrote a template with {len(sections)} section(s) to {args.template}")
        elif args.since:
            before = earlier_sections(args.since)
            counts = {"unchanged": 0, "changed": 0, "new": 0}
            for title, section_digest in sections.items():
                state = "new" if title not in before else "unchanged" if before[title] == section_digest else "changed"
                counts[state] += 1
                print(f"{state:9} {title}")
            gone = [title for title in before if title not in sections]
            for title in gone:
                print(f"gone      {title}")
            print(f"ledger review sections: {len(sections)} section(s): {counts['unchanged']} unchanged, "
                  f"{counts['changed']} changed, {counts['new']} new; {len(gone)} earlier section(s) gone")
        else:
            for title, section_digest in sections.items():
                print(f"{section_digest[:16]}  {title}")
            print(f"ledger review sections: {len(sections)} section(s)")
    except (ValueError, OSError, KeyError) as exc:
        print(f"ledger review sections: ERROR: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
