#!/usr/bin/env python3
"""Verify preserved source identity, audit coverage and the pinned dependency set."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from check_axioms import read_targets


def verify(root, dependency_check=False):
    root = Path(root).resolve()
    spec = json.loads((root / "ci/source-integrity.json").read_text())
    for name, digest in spec["files"].items():
        path = root / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"Preserved file changed or missing: {name}")
    preserved = {name for name in spec["files"] if name.endswith(".lean")}
    if len(preserved) != spec["preserved_lean_files"]:
        raise ValueError("Preserved Lean file count mismatch")
    actual = {
        str(path.relative_to(root)) for path in root.rglob("*.lean")
        if not any(part in {".git", ".lake", "ci-results"} for part in path.relative_to(root).parts)
    }
    if actual != preserved | {"ci/EndpointTypes.lean"}:
        raise ValueError(f"Unexpected source inventory difference: {actual ^ (preserved | {'ci/EndpointTypes.lean'})}")
    targets = read_targets(root / "audit-targets.tsv")
    if len(targets) != spec["expected_audit_targets"]:
        raise ValueError("Audit target count changed")
    audit = (root / "TwoRoutesAudit.lean").read_text()
    printed = re.findall(r"^#print axioms (\S+)$", audit, re.M)
    if printed != targets:
        raise ValueError("Final audit and target plan differ")
    modules = (root / "compile-order.txt").read_text().splitlines()
    if len(modules) != 117 or set(modules) | {"TwoRoutesAudit.lean"} != preserved:
        raise ValueError("Compile plan does not cover all preserved sources")
    pins = json.loads((root / "ci/dependency-pins.json").read_text())
    if (root / "lean-toolchain").read_text().strip() != pins["toolchain"]:
        raise ValueError("Lean toolchain pin changed")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    dependencies = {p["name"]: p["rev"] for p in manifest["packages"]}
    if dependencies != pins["packages"] or len(dependencies) != len(manifest["packages"]):
        raise ValueError("Lake manifest dependency pins changed")
    if dependency_check:
        for name, revision in pins["packages"].items():
            package = root / ".lake/packages" / name
            actual_rev = subprocess.check_output(
                ["git", "-C", str(package), "rev-parse", "HEAD"], text=True
            ).strip()
            if actual_rev != revision:
                raise ValueError(f"Checked-out dependency differs: {name}")
        if (root / ".lake/packages/mathlib/lean-toolchain").read_text().strip() != pins["toolchain"]:
            raise ValueError("Mathlib toolchain differs")
    print(f"SOURCE_IDENTITY=PASS|LEAN_FILES={len(preserved)}|AUDIT_TARGETS={len(targets)}")
    print("TARGET=GITHUB_CI")
    print("PROJECT_ANCHOR=" + spec["project_anchor"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".")
    parser.add_argument("--dependencies", action="store_true")
    args = parser.parse_args()
    verify(args.root, args.dependencies)
