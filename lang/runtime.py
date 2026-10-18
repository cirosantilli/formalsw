"""Locate a writable Lake workspace for checkout and installed CLI use."""

from functools import cache
import hashlib
import os
from pathlib import Path
import shutil
import sys


@cache
def lake_root():
    """
    Use the caller's Lake project, or cache the bundled sources under .formalsw.

    Hash the sources so upgrades cannot reuse objects from a different release.
    The installed wheel remains read-only, including under pipx or system pip.
    """
    project = Path.cwd()
    if any((project / name).is_file() for name in ('lakefile.lean', 'lakefile.toml')):
        return project
    bundled = Path(__file__).resolve().parent.parent
    files = [bundled / name for name in ('formalsw', 'FormalSW.lean', 'lakefile.toml', 'lean-toolchain')]
    files += sorted(path for path in (bundled / 'lang').rglob('*')
                    if path.suffix in ('.py', '.lean') and '__pycache__' not in path.parts)
    digest = hashlib.sha256()
    for path in files:
        digest.update(str(path.relative_to(bundled)).encode() + b'\0')
        digest.update(path.read_bytes() + b'\0')
    root = project / '.formalsw' / 'runtime' / digest.hexdigest()
    for path in files:
        target = root / path.relative_to(bundled)
        if not target.exists() or target.read_bytes() != path.read_bytes():
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
    return root


def lake_command(*arguments):
    return ['lake', '-d', str(lake_root()), *arguments]


def runtime_env():
    env = dict(os.environ, FORMALSW_PYTHON=sys.executable)
    root = lake_root()
    if root != Path.cwd():
        # Elan chooses a toolchain before Lake processes -d.
        env['ELAN_TOOLCHAIN'] = (root / 'lean-toolchain').read_text().strip()
    return env
