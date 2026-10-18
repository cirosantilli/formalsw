"""Shared helpers for CLI regression tests."""
from pathlib import Path
from tempfile import TemporaryDirectory


def project_temporary_directory(*, prefix):
    """Create ignored scratch files inside the project for source-bound proofs."""
    scratch = Path(__file__).resolve().parents[2] / '.test-tmp'
    scratch.mkdir(exist_ok=True)
    return TemporaryDirectory(prefix=prefix, dir=scratch)
