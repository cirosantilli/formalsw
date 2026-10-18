"""Python setup shared by source-language annotation frontends."""

from contextlib import contextmanager
from pathlib import Path
import sys
import tomllib


class SetupError(ValueError):
    pass


def python_paths(project: Path) -> list[str]:
    """Resolve configured import roots relative to the checking project."""
    config = project / 'pyproject.toml'
    try:
        settings = tomllib.loads(config.read_text()) if config.is_file() else {}
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise SetupError(f'{config}: {error}') from error
    tool = settings.get('tool', {})
    options = tool.get('formalsw', {}) if isinstance(tool, dict) else None
    if not isinstance(options, dict):
        raise SetupError('[tool.formalsw] must be a TOML table')
    paths = options.get('python-path', [])
    if not isinstance(paths, list) or any(not isinstance(path, str) for path in paths):
        raise SetupError('[tool.formalsw].python-path must be a list of paths')
    return [str((project / path).resolve()) for path in paths]


@contextmanager
def import_paths(source: Path):
    original = sys.path[:]
    project = Path.cwd().resolve()
    sys.path[:0] = [*python_paths(project), str(source.resolve().parent), str(project)]
    try:
        yield
    finally:
        sys.path[:] = original


def initial_environment(source: Path) -> dict:
    return {'__name__': '__formalsw_spec__', '__file__': str(source.resolve())}


def execute(code: str, environment: dict, source: Path, line: int) -> None:
    """Execute one explicit Py directive; preserve Python statement semantics."""
    try:
        with import_paths(source):
            exec(compile('\n' * (line - 1) + code, str(source), 'exec'), environment)
    except (Exception, SystemExit) as error:
        raise SetupError(f'{source}:{line}: Py setup failed: {type(error).__name__}: {error}') from error


def evaluate(expression: str, environment: dict, source: Path, line: int):
    try:
        with import_paths(source):
            return eval(compile('\n' * (line - 1) + expression, str(source), 'eval'), environment)
    except (Exception, SystemExit) as error:
        raise SetupError(f'{source}:{line}: specification expression failed: {type(error).__name__}: {error}') from error
