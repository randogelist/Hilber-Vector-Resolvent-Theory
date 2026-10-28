#!/usr/bin/env python3
"""Typeset the mathematical preprint; requires TeX Live and invokes no Lean tools."""
from pathlib import Path
import argparse
import shutil
import subprocess
import tempfile


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=here / 'RH_H00_Two_Routes_Native_PASS_and_GitHub_CI.pdf')
    args = parser.parse_args()
    compiler = shutil.which('pdflatex')
    if compiler is None:
        parser.error('Install pdflatex (TeX Live) with the packages in preprint.tex.')
    with tempfile.TemporaryDirectory(prefix='rh-preprint-') as temporary:
        directory = Path(temporary)
        command = [compiler, '-interaction=nonstopmode', '-halt-on-error',
                   f'-output-directory={directory}', str(here / 'preprint.tex')]
        for _ in range(3):
            result = subprocess.run(command, cwd=here, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                raise RuntimeError(result.stdout)
        log = (directory / 'preprint.log').read_text()
        if 'Overfull \\hbox' in log or 'There were undefined references' in log:
            raise RuntimeError('Typesetting needs review:\n' + log)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(directory / 'preprint.pdf', args.output)
    print(args.output)


if __name__ == '__main__':
    main()
