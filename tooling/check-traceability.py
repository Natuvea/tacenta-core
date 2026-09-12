#!/usr/bin/env python3
"""Check the security-property traceability spine.

This is a structural gate, not a proof auditor. It keeps the security
requirement pages, the assumptions page and the limitations status ledger from
drifting apart while the deeper claim/vector/test index is built.
"""
from __future__ import annotations

import re
import sys
from argparse import ArgumentParser
from dataclasses import dataclass
from pathlib import Path

REQ_HEADING = re.compile(r"^### (REQ-[A-Z]+-\d+): (.+)$", re.M)
ASM_HEADING = re.compile(r"^### (ASM-\d+): (.+)$", re.M)
ID_RE = re.compile(r"\b(REQ-[A-Z]+-\d+|ASM-\d+|LIM-\d+|ADV-\d+|AS-\d+|EX-\d+)\b")
STATUS_RE = re.compile(r"^- \*\*Status: ([^*]+)\*\*", re.M)
RESTS_RE = re.compile(r"^- \*\*Rests on:\*\* (.*?)(?:\n- \*\*|\Z)", re.M | re.S)
RELIED_RE = re.compile(r"^- \*\*Relied on by:\*\* (.*?)(?:\n- \*\*|\Z)", re.M | re.S)
LIMIT_ROW_RE = re.compile(r"^\| (REQ-[A-Z]+-\d+): ([^|]+) \| ([^|]+) \|$", re.M)


@dataclass(frozen=True)
class Requirement:
    id: str
    title: str
    path: Path
    body: str
    status: str
    assumptions: set[str]


def norm_status(s: str) -> str:
    s = s.strip().rstrip(".").rstrip(",").lower()
    return re.sub(r"\s+", " ", s)


def status_class(s: str) -> str:
    s = norm_status(s)
    if s.startswith("proved"):
        return "proved"
    if s.startswith("assumed"):
        return "assumed"
    if s.startswith("tested only"):
        return "tested only"
    return s


def collect_headings(pattern: re.Pattern[str], path: Path) -> dict[str, str]:
    return {m.group(1): m.group(2).strip() for m in pattern.finditer(path.read_text())}


def split_sections(text: str, pattern: re.Pattern[str]) -> list[tuple[str, str, str]]:
    matches = list(pattern.finditer(text))
    out: list[tuple[str, str, str]] = []
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        out.append((match.group(1), match.group(2).strip(), text[match.end():end]))
    return out


def load_requirements(security: Path, errors: list[str]) -> dict[str, Requirement]:
    reqs: dict[str, Requirement] = {}
    for path in sorted(security.glob("*.md")):
        if path.name == "limitations.md":
            continue
        text = path.read_text()
        for rid, title, body in split_sections(text, REQ_HEADING):
            if rid in reqs:
                errors.append(f"duplicate requirement id {rid}: {path} and {reqs[rid].path}")
                continue
            status_m = STATUS_RE.search(body)
            rests_m = RESTS_RE.search(body)
            if not status_m:
                errors.append(f"{path}: {rid} has no '- **Status:**' line")
                status = ""
            else:
                status = status_m.group(1).strip()
            if not rests_m:
                errors.append(f"{path}: {rid} has no '- **Rests on:**' line")
                assumptions = set()
            else:
                assumptions = set(re.findall(r"\bASM-\d+\b", rests_m.group(1)))
                if not assumptions:
                    errors.append(f"{path}: {rid} names no ASM-* in '- **Rests on:**'")
            reqs[rid] = Requirement(rid, title, path, body, status, assumptions)
    return reqs


def check_limitations(security: Path, reqs: dict[str, Requirement], errors: list[str]) -> None:
    path = security / "limitations.md"
    rows = {
        match.group(1): (match.group(2).strip(), match.group(3).strip())
        for match in LIMIT_ROW_RE.finditer(path.read_text())
    }
    if set(rows) != set(reqs):
        for missing in sorted(set(reqs) - set(rows)):
            errors.append(f"{path}: missing status-table row for {missing}")
        for extra in sorted(set(rows) - set(reqs)):
            errors.append(f"{path}: status-table row for unknown {extra}")
    for rid, req in sorted(reqs.items()):
        if rid not in rows:
            continue
        row_title, row_status = rows[rid]
        if row_title != req.title:
            errors.append(f"{path}: {rid} title differs from {req.path}: {row_title!r} != {req.title!r}")
        if status_class(row_status) != status_class(req.status):
            errors.append(f"{path}: {rid} status class differs from {req.path}: {row_status!r} != {req.status!r}")


def check_assumptions(threat: Path, reqs: dict[str, Requirement], errors: list[str]) -> set[str]:
    path = threat / "assumptions.md"
    text = path.read_text()
    assumptions = collect_headings(ASM_HEADING, path)
    cited = {assumption for req in reqs.values() for assumption in req.assumptions}
    for asm in sorted(cited - set(assumptions)):
        errors.append(f"requirements cite unknown assumption {asm}")

    sections = {aid: body for aid, _title, body in split_sections(text, ASM_HEADING)}
    for aid, body in sorted(sections.items()):
        relied_m = RELIED_RE.search(body)
        if not relied_m:
            errors.append(f"{path}: {aid} has no '- **Relied on by:**' line")
            continue
        relied_text = relied_m.group(1)
        direct_list = set(re.findall(r"\bREQ-[A-Z]+-\d+\b", relied_text))
        from_requirements = {req.id for req in reqs.values() if aid in req.assumptions}
        # Some assumptions deliberately state broader indirect scope in prose,
        # for example "through ASM-04" or "every requirement whose status is
        # proved". Their direct list is still checked for known IDs by the
        # identifier pass, but the prose is not treated as an exact inverse.
        broad = "every requirement" in relied_text or "through ASM-" in relied_text
        if broad:
            continue
        if direct_list != from_requirements:
            for missing in sorted(from_requirements - direct_list):
                errors.append(f"{path}: {aid} is cited by {missing} but its relied-on list omits it")
            for extra in sorted(direct_list - from_requirements):
                errors.append(f"{path}: {aid} lists {extra}, but that requirement does not cite {aid}")
    return set(assumptions)


def check_identifier_references(security: Path, threat: Path, reqs: dict[str, Requirement], assumptions: set[str], errors: list[str]) -> None:
    known: set[str] = set(reqs) | assumptions
    for directory, pattern in [
        (threat, r"^#+ (AS-\d+|ADV-\d+|EX-\d+):"),
        (security, r"^#+ (LIM-\d+):"),
    ]:
        rx = re.compile(pattern, re.M)
        for path in sorted(directory.glob("*.md")):
            known.update(match.group(1) for match in rx.finditer(path.read_text()))

    for path in sorted(list(security.glob("*.md")) + list(threat.glob("*.md"))):
        text = path.read_text()
        for ref in sorted(set(ID_RE.findall(text))):
            if ref not in known:
                errors.append(f"{path}: references unknown identifier {ref}")


def main() -> int:
    parser = ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    security = root / "tacenta-spec" / "security-properties"
    threat = root / "tacenta-spec" / "threat-model"

    errors: list[str] = []
    reqs = load_requirements(security, errors)
    check_limitations(security, reqs, errors)
    assumptions = check_assumptions(threat, reqs, errors)
    check_identifier_references(security, threat, reqs, assumptions, errors)

    if errors:
        for err in errors:
            print(f"traceability: ERROR: {err}", file=sys.stderr)
        return 1
    print(
        "traceability: "
        f"{len(reqs)} requirements, {len(assumptions)} assumptions and identifier references are consistent"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
