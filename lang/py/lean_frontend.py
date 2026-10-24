"""Parse specification headers with Lean, sharing one parser process per CLI."""
import atexit
from contextlib import contextmanager
import json
import os
import shutil
import sys
import subprocess
from pathlib import Path

from .trial import ScenarioError
from lang.runtime import lake_command, runtime_env


_parser = None
_environment = None
_session_depth = 0


def _close():
    global _parser
    if _parser is not None:
        _parser.stdin.close()
        _parser.wait(timeout=10)
        _parser = None


atexit.register(_close)


@contextmanager
def lean_session():
    """Share setup within a check, then discard it before the next invocation."""
    global _session_depth, _environment
    if _session_depth == 0:
        _close()
        _environment = None
    _session_depth += 1
    try:
        yield
    finally:
        _session_depth -= 1
        if _session_depth == 0:
            _close()
            _environment = None


def lean_env():
    """Build once per session and prioritize the caller's generated Lean objects."""
    global _environment
    if _environment is not None:
        return _environment
    if shutil.which('lake') is None:
        raise ScenarioError('required executable not found on PATH: lake')
    built = subprocess.run(lake_command('build', 'FormalSW', 'lang.py.FormalSW'),
                           env=runtime_env(), capture_output=True, text=True)
    if built.returncode:
        raise ScenarioError('failed to build the FormalSW core or Python model:\n'
                            + built.stdout + built.stderr)
    completed = subprocess.run(
        lake_command('env', sys.executable, '-c',
                     'import json, os; print(json.dumps(dict(os.environ)))'),
        env=runtime_env(), text=True, capture_output=True,
    )
    if completed.returncode:
        raise ScenarioError('failed to prepare the Lean environment:\n'
                            + completed.stdout + completed.stderr)
    env = json.loads(completed.stdout)
    # Dependencies may have their own .formalsw namespace. Keep this project's
    # AST and proof objects ahead of Lake's dependency paths.
    paths = [str(Path.cwd() / '.lake/build/lib/lean'), '.']
    if env.get('LEAN_PATH'):
        paths.append(env['LEAN_PATH'])
    env['LEAN_PATH'] = os.pathsep.join(paths)
    if _session_depth:
        _environment = env
    return env


def _request(request):
    global _parser
    if _parser is None:
        environment = lean_env()
        frontend = Path(__file__).with_name('spec_frontend.lean').resolve()
        _parser = subprocess.Popen(['lean', '--run', str(frontend)], env=environment,
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, text=True)
    _parser.stdin.write(json.dumps(request) + '\n')
    _parser.stdin.flush()
    line = _parser.stdout.readline()
    try:
        result = json.loads(line)
    except ValueError as error:
        _parser.terminate()
        output, diagnostics = _parser.communicate(timeout=10)
        _parser = None
        raise ScenarioError('Lean specification parser failed: ' + line + output + diagnostics) from error
    if 'error' in result:
        raise ScenarioError(result['error'])
    return result


def parse_theorem(text):
    return _request(text)


def parse_imports(text):
    """Return import names as components, using Lean's actual header parser."""
    return _request({"imports": text})["imports"]


def guard_proposition(proposition, condition, captures, inputs, bound):
    """Place a domain premise inside the native quantifiers binding its inputs."""
    return _request({"guard": proposition, "condition": condition,
                     "captures": captures, "inputs": inputs, "bound": list(bound)})
