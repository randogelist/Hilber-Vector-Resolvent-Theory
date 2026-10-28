#!/usr/bin/env python3
"""Build and validate the 50-page preprint; never invokes Lean or Lake."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent
NAME = "Hilbert_Vector_Resolvent_Theory_Preprint_50pp_v0_1.pdf"


def build(destination: Path) -> None:
    for executable in ("pdflatex", "pdfinfo"):
        if not shutil.which(executable):
            raise SystemExit(f"Required executable not found: {executable}")
    env = os.environ.copy()
    env.setdefault("SOURCE_DATE_EPOCH", "1793145600")  # 2026-10-28 00:00 UTC
    env.setdefault("FORCE_SOURCE_DATE", "1")
    with tempfile.TemporaryDirectory(prefix="hvr50-") as scratch:
        scratch = Path(scratch)
        for _ in range(3):
            run = subprocess.run(
                ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
                 "-halt-on-error", f"-output-directory={scratch}", "preprint.tex"],
                cwd=ROOT, env=env, capture_output=True, text=True,
            )
            if run.returncode:
                raise SystemExit(run.stdout[-8000:])
        log = (scratch / "preprint.log").read_text()
        mapping = [(int(a), int(b)) for a, b in re.findall(r"HVRPAGE\|(\d+)\|(\d+)", log)]
        if mapping != [(n, n) for n in range(1, 51)]:
            raise SystemExit(f"Thematic page mapping is incorrect: {mapping}")
        forbidden = [r"Overfull \\[hv]box", r"LaTeX(?: Font)? Warning:",
                     r"undefined references", r"undefined on input line"]
        errors = [pattern for pattern in forbidden if re.search(pattern, log)]
        if errors:
            lines = log.splitlines()
            details = []
            for index, line in enumerate(lines):
                if any(re.search(pattern, line) for pattern in forbidden):
                    details.extend(lines[index:index + 6])
            raise SystemExit(f"LaTeX validation failed: {errors}\n" + "\n".join(details))
        pdf = scratch / "preprint.pdf"
        info = subprocess.check_output(["pdfinfo", str(pdf)], text=True)
        match = re.search(r"^Pages:\s+(\d+)\s*$", info, re.M)
        if not match or int(match.group(1)) != 50:
            raise SystemExit("The PDF does not have exactly fifty pages")
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(pdf, destination)
        report = {
            "manuscript": NAME,
            "pages": 50,
            "thematic_page_mapping": "PASS: 1 through 50",
            "overfull_boxes": 0,
            "latex_warnings": 0,
            "local_lean_or_lake_executed": False,
            "formal_source_baseline": "c6b95fd9e3d792270026da083bddddbc72bacb22",
            "sha256": hashlib.sha256(destination.read_bytes()).hexdigest(),
        }
        destination.with_suffix(".build.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))
        print(destination)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / NAME)
    args = parser.parse_args()
    build(args.output.resolve())
