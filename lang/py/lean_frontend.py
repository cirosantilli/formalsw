"""Parse specification headers with Lean, sharing one parser process per CLI."""
import atexit
import json
import subprocess

from .concurrent_spec import ScenarioError


_parser = None


def _close():
    global _parser
    if _parser is not None:
        _parser.stdin.close()
        _parser.wait(timeout=10)
        _parser = None


atexit.register(_close)


def parse_theorem(text):
    global _parser
    if _parser is None:
        built = subprocess.run(['lake', 'build', 'FormalSW'], capture_output=True, text=True)
        if built.returncode:
            raise ScenarioError('failed to build Lean specification parser:\n' + built.stdout + built.stderr)
        _parser = subprocess.Popen(['lake', 'env', 'lean', '--run', 'lang/py/spec_frontend.lean'],
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, text=True)
    _parser.stdin.write(json.dumps(text) + '\n')
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
