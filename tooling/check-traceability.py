#!/usr/bin/env python3
"""Check the security-property traceability spine.

This is a structural gate, not a proof auditor. It keeps the security
requirement pages, the assumptions page and the limitations status ledger from
drifting apart. It also checks the pilot evidence index links for the P2
requirements without deciding whether a theorem or test semantically proves a
requirement.
"""
from __future__ import annotations

import json
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
THEOREM_RE = r"\btheorem\s+{name}\b"
TEST_RE = r"\bfn\s+{name}\s*\("
ENTRY_REQUIRED_KEYS = {
    "id",
    "source",
    "property",
    "status",
    "assumptions",
    "limitations",
    "implementation",
    "model_properties",
    "claims",
    "vectors",
    "tests",
    "missing_evidence",
}
ENTRY_LIST_KEYS = {
    "assumptions",
    "limitations",
    "implementation",
    "model_properties",
    "claims",
    "vectors",
    "tests",
    "missing_evidence",
}


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


def collect_known_ids(security: Path, threat: Path, reqs: dict[str, Requirement], assumptions: set[str]) -> set[str]:
    known: set[str] = set(reqs) | assumptions
    for directory, pattern in [
        (threat, r"^#+ (AS-\d+|ADV-\d+|EX-\d+):"),
        (security, r"^#+ (LIM-\d+):"),
    ]:
        rx = re.compile(pattern, re.M)
        for path in sorted(directory.glob("*.md")):
            known.update(match.group(1) for match in rx.finditer(path.read_text()))
    return known


def require_text(path: Path, what: str, errors: list[str]) -> str:
    if not path.exists():
        errors.append(f"evidence index references missing {what} path {path}")
        return ""
    return path.read_text()


def check_symbol(root: Path, item: dict, key: str, errors: list[str]) -> None:
    if not isinstance(item, dict):
        errors.append(f"evidence index {key} entry must be an object")
        return
    name = item.get(key)
    if not isinstance(name, str) or not name:
        errors.append(f"evidence index entry in {item.get('path', '<missing path>')} has no {key}")
        return
    path_value = item.get("path")
    if not isinstance(path_value, str):
        errors.append(f"evidence index {key} {name} has no path")
        return
    text = require_text(root / path_value, key, errors)
    if text and name not in text:
        errors.append(f"evidence index {key} {name} not found in {path_value}")


def check_theorem(root: Path, item: dict, errors: list[str]) -> None:
    if not isinstance(item, dict):
        errors.append("evidence index model property entry must be an object")
        return
    coverage = item.get("coverage")
    if not isinstance(coverage, str) or not coverage.strip():
        errors.append(f"evidence index model property in {item.get('path', '<missing path>')} has no coverage")
    theorem = item.get("theorem")
    if not isinstance(theorem, str) or not theorem:
        errors.append(f"evidence index model property in {item.get('path', '<missing path>')} has no theorem")
        return
    path_value = item.get("path")
    if not isinstance(path_value, str):
        errors.append(f"evidence index theorem {theorem} has no path")
        return
    text = require_text(root / path_value, "theorem", errors)
    if text and not re.search(THEOREM_RE.format(name=re.escape(theorem)), text):
        errors.append(f"evidence index theorem {theorem} not found in {path_value}")


def check_test(root: Path, item: dict, errors: list[str]) -> None:
    if not isinstance(item, dict):
        errors.append("evidence index test entry must be an object")
        return
    coverage = item.get("coverage")
    if not isinstance(coverage, str) or not coverage.strip():
        errors.append(f"evidence index test in {item.get('path', '<missing path>')} has no coverage")
    name = item.get("name")
    if not isinstance(name, str) or not name:
        errors.append(f"evidence index test in {item.get('path', '<missing path>')} has no name")
        return
    path_value = item.get("path")
    if not isinstance(path_value, str):
        errors.append(f"evidence index test {name} has no path")
        return
    text = require_text(root / path_value, "test", errors)
    if text and not re.search(TEST_RE.format(name=re.escape(name)), text):
        errors.append(f"evidence index test {name} not found in {path_value}")


def check_vector(root: Path, item: dict, errors: list[str]) -> None:
    if not isinstance(item, dict):
        errors.append("evidence index vector entry must be an object")
        return
    coverage = item.get("coverage")
    if not isinstance(coverage, str) or not coverage.strip():
        errors.append(f"evidence index vector {item.get('path', '<missing path>')} has no coverage")
    path_value = item.get("path")
    if not isinstance(path_value, str):
        errors.append("evidence index vector entry has no path")
        return
    path = root / path_value
    if not path.exists():
        errors.append(f"evidence index references missing vector path {path}")
        return
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        errors.append(f"evidence index vector path {path_value} is not JSON: {exc}")
        return
    case_ids = item.get("case_ids")
    if not isinstance(case_ids, list) or not case_ids:
        errors.append(f"evidence index vector {path_value} has no case_ids")
        return
    available = {
        v.get("id")
        for key in ("vectors", "cases")
        for v in data.get(key, [])
        if isinstance(v, dict)
    }
    for case_id in case_ids:
        if case_id not in available:
            errors.append(f"evidence index vector case {case_id} not found in {path_value}")


def check_claim(root: Path, item: dict, errors: list[str]) -> None:
    if not isinstance(item, dict):
        errors.append("evidence index claim entry must be an object")
        return
    path_value = item.get("path")
    if not isinstance(path_value, str):
        errors.append("evidence index claim entry has no path")
        return
    text = require_text(root / path_value, "claim", errors)
    if not text:
        return
    section = item.get("section")
    if not isinstance(section, str) or section not in text:
        errors.append(f"evidence index claim section {section!r} not found in {path_value}")
    refs = item.get("references")
    if not isinstance(refs, list) or not refs:
        errors.append(f"evidence index claim {path_value} has no references")
        return
    for ref in refs:
        if not isinstance(ref, str) or ref not in text:
            errors.append(f"evidence index claim reference {ref} not found in {path_value}")


def check_evidence_index(root: Path, security: Path, reqs: dict[str, Requirement], known_ids: set[str], errors: list[str]) -> None:
    path = security / "evidence-index.json"
    if not path.exists():
        errors.append(f"{path}: missing evidence index")
        return
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        errors.append(f"{path}: invalid JSON: {exc}")
        return
    if data.get("schema_version") != 1:
        errors.append(f"{path}: schema_version must be 1")
    entries = data.get("requirements")
    if not isinstance(entries, list) or not entries:
        errors.append(f"{path}: requirements must be a non-empty list")
        return
    seen: set[str] = set()
    for entry in entries:
        if not isinstance(entry, dict):
            errors.append(f"{path}: requirement entries must be objects")
            continue
        for key in sorted(ENTRY_REQUIRED_KEYS - set(entry)):
            errors.append(f"{path}: evidence entry missing required field {key}")
        for key in sorted(ENTRY_LIST_KEYS):
            if key in entry and not isinstance(entry[key], list):
                errors.append(f"{path}: evidence field {key} must be a list")
        rid = entry.get("id")
        if not isinstance(rid, str) or rid not in reqs:
            errors.append(f"{path}: evidence entry references unknown requirement {rid}")
            continue
        if rid in seen:
            errors.append(f"{path}: duplicate evidence entry for {rid}")
        seen.add(rid)
        status = entry.get("status")
        if status_class(str(status)) != status_class(reqs[rid].status):
            errors.append(f"{path}: {rid} evidence status {status!r} differs from requirement status {reqs[rid].status!r}")
        source = entry.get("source")
        if not isinstance(source, str) or not source.endswith(f"#{rid}"):
            errors.append(f"{path}: {rid} source must end with #{rid}")
        prop = entry.get("property")
        if not isinstance(prop, str) or not prop.strip():
            errors.append(f"{path}: {rid} property must be a non-empty string")
        for asm in entry.get("assumptions", []):
            if asm not in known_ids or not asm.startswith("ASM-"):
                errors.append(f"{path}: {rid} cites unknown assumption {asm}")
        for lim in entry.get("limitations", []):
            if lim not in known_ids or not lim.startswith("LIM-"):
                errors.append(f"{path}: {rid} cites unknown limitation {lim}")
        for item in entry.get("implementation", []):
            check_symbol(root, item, "symbol", errors)
        for item in entry.get("model_properties", []):
            check_theorem(root, item, errors)
        for item in entry.get("claims", []):
            check_claim(root, item, errors)
        for item in entry.get("vectors", []):
            check_vector(root, item, errors)
        for item in entry.get("tests", []):
            check_test(root, item, errors)
        missing = entry.get("missing_evidence", [])
        if status_class(reqs[rid].status) != "proved" and not missing:
            errors.append(f"{path}: {rid} needs explicit missing_evidence for non-proved status")
        for item in missing:
            if not isinstance(item, dict):
                errors.append(f"{path}: {rid} missing_evidence entry must be an object")
                continue
            for key in ("kind", "reason", "references"):
                if key not in item:
                    errors.append(f"{path}: {rid} missing_evidence entry missing {key}")
            for key in ("kind", "reason"):
                if key in item and (not isinstance(item[key], str) or not item[key].strip()):
                    errors.append(f"{path}: {rid} missing_evidence {key} must be a non-empty string")
            refs = item.get("references") if isinstance(item, dict) else None
            if not isinstance(refs, list) or not refs:
                errors.append(f"{path}: {rid} missing_evidence entry has no references")
                continue
            for ref in refs:
                if ref not in known_ids:
                    errors.append(f"{path}: {rid} missing_evidence cites unknown reference {ref}")


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
    known_ids = collect_known_ids(security, threat, reqs, assumptions)
    check_evidence_index(root, security, reqs, known_ids, errors)

    if errors:
        for err in errors:
            print(f"traceability: ERROR: {err}", file=sys.stderr)
        return 1
    print(
        "traceability: "
        f"{len(reqs)} requirements, {len(assumptions)} assumptions, identifier references "
        "and the evidence index are consistent"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
