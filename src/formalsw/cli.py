"""Run the bundled checker with its language models available to Python."""

from pathlib import Path
import runpy
import sys


def main():
    runtime = Path(__file__).resolve().parent / '_runtime'
    if not runtime.is_dir():
        # Development checkout; release wheels bundle the same files below _runtime.
        runtime = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(runtime))
    runpy.run_path(str(runtime / 'formalsw'), run_name='__main__')
