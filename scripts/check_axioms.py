#!/usr/bin/env python3
"""Fail-closed parser for a fresh, complete TwoRoutesAudit.lean invocation."""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
MARKER = re.compile(r'^"?AXIOM_(BEGIN|END)\|([A-Za-z_][A-Za-z0-9_.]*)"?$')
RECORD = re.compile(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
)


def read_targets(path):
    targets = []
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("|")
        if len(fields) != 2 or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", fields[1]):
            raise ValueError(f"Malformed audit target: {line!r}")
        targets.append(fields[1])
    if not targets or len(set(targets)) != len(targets):
        raise ValueError("Empty or duplicate audit targets")
    return targets


def check_output(text, expected):
    if not expected or len(set(expected)) != len(expected):
        raise ValueError("Expected declaration list must be nonempty and unique")
    if re.search(r"sorryAx|(^|\s)error(?:\(|:)|declaration uses ['`]sorry", text, re.M):
        raise ValueError("Compiler error or admitted proof in audit output")
    records = {}
    current = None
    body = []
    order = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        marker = MARKER.fullmatch(stripped)
        if marker:
            kind, name = marker.groups()
            if kind == "BEGIN":
                if current is not None or name in records:
                    raise ValueError(f"Nested or duplicate audit block: {name}")
                if name not in expected:
                    raise ValueError(f"Unexpected declaration: {name}")
                current, body = name, []
                continue
            if current != name:
                raise ValueError(f"Unmatched audit end: {name}")
            record = RECORD.fullmatch("\n".join(body).strip())
            if record is None or record.group(1) != name:
                raise ValueError(f"Missing, duplicate or malformed axiom record: {name}")
            axiom_text = record.group(2)
            axioms = [x.strip() for x in axiom_text.split(",")] if axiom_text and axiom_text.strip() else []
            if len(axioms) != len(set(axioms)):
                raise ValueError(f"Duplicate axiom names: {name}")
            if set(axioms) - ALLOWED:
                raise ValueError(f"Unapproved axioms in {name}: {sorted(set(axioms) - ALLOWED)}")
            records[name] = axioms
            order.append(name)
            current, body = None, []
        elif current is not None:
            body.append(line)
        else:
            raise ValueError(f"Unexpected text outside audit block: {stripped[:160]}")
    if current is not None:
        raise ValueError(f"Truncated audit block: {current}")
    if order != list(expected):
        missing = sorted(set(expected) - set(records))
        raise ValueError(f"Audit coverage or declaration order differs; missing: {missing}")
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--targets", default="audit-targets.tsv")
    parser.add_argument("--log", default="ci-results/axioms.log")
    parser.add_argument("--output", default="ci-results/axiom-audit.json")
    args = parser.parse_args()
    targets = read_targets(args.targets)
    raw = Path(args.log).read_bytes()
    records = check_output(raw.decode("utf-8"), targets)
    report = {
        "target": "GITHUB_CI",
        "status": "PASS",
        "declarations_audited": len(records),
        "allowed_axioms": sorted(ALLOWED),
        "log_sha256": hashlib.sha256(raw).hexdigest(),
        "targets_sha256": hashlib.sha256(Path(args.targets).read_bytes()).hexdigest(),
        "axioms_by_declaration": records,
        "H00_admissibility": "OPEN",
        "unconditional_RH": "NOT_ESTABLISHED",
    }
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"GITHUB_CI_AXIOM_AUDIT=PASS|DECLARATIONS={len(records)}")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, UnicodeError) as error:
        print(f"GITHUB_CI_AXIOM_AUDIT=FAIL|{error}", file=sys.stderr)
        sys.exit(1)
