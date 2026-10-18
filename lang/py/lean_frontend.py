"""Parse specification headers with Lean, sharing one parser process per CLI."""
import atexit
import json
import subprocess
from pathlib import Path

from .trial import ScenarioError
from lang.runtime import lake_command, runtime_env


_parser = None


def _close():
    global _parser
    if _parser is not None:
        _parser.stdin.close()
        _parser.wait(timeout=10)
        _parser = None


atexit.register(_close)


def _request(request):
    global _parser
    if _parser is None:
        built = subprocess.run(lake_command('build', 'FormalSW'), env=runtime_env(), capture_output=True, text=True)
        if built.returncode:
            raise ScenarioError('failed to build Lean specification parser:\n' + built.stdout + built.stderr)
        frontend = Path(__file__).with_name('spec_frontend.lean').resolve()
        _parser = subprocess.Popen(lake_command('env', 'lean', '--run', str(frontend)), env=runtime_env(),
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
