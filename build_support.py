"""Bundle the checker and Lean sources beside the Python entry point."""

from pathlib import Path

from setuptools.command.build_py import build_py


ROOT = Path(__file__).resolve().parent


def runtime_files():
    for name in ('formalsw', 'FormalSW.lean', 'lakefile.toml', 'lean-toolchain'):
        yield ROOT / name
    yield from sorted(path for path in (ROOT / 'lang').rglob('*')
                      if path.suffix in ('.py', '.lean') and '__pycache__' not in path.parts)


class BuildPy(build_py):
    def run(self):
        super().run()
        for source in runtime_files():
            target = Path(self.build_lib) / 'formalsw' / '_runtime' / source.relative_to(ROOT)
            self.mkpath(str(target.parent))
            self.copy_file(str(source), str(target))

    def get_outputs(self, include_bytecode=True):
        return super().get_outputs(include_bytecode) + [
            str(Path(self.build_lib) / 'formalsw' / '_runtime' / source.relative_to(ROOT))
            for source in runtime_files()
        ]
