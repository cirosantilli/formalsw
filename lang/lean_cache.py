"""
Reuse successful Lean compilations with conservative dependency validation.

Requirements wrappers must still be compiled by the caller. This cache only
reuses objects produced by successful compilation of the same source against
the same transitive imports, toolchain, frontend, options, and environment.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat as stat_mode
import subprocess
import sys
import tempfile


_SCHEMA = 1
_EFFECTS = re.compile(
    r'\b(?:elab|elab_rules|macro|macro_rules|initialize|builtin_initialize|'
    r'run_tac|run_cmd|run_meta|unsafe|implemented_by|extern|IO|EIO|BaseIO|'
    r'System|Process|Environment|importModules|loadDynlib)\b|'
    r'#\s*(?:eval|eval!|exec|run)\b|\bLean\.(?:Elab|Meta|Core)\b'
)
_INCLUDE = re.compile(r'\b(include_str|include_bytes|include_bin)\b')
_LITERAL = re.compile(r'\s*("(?:[^"\\]|\\.)*")')
_LIBRARIES = {
    'mathlib': {'Mathlib', 'Archive', 'Counterexamples'},
    'batteries': {'Batteries'},
    'aesop': {'Aesop'},
    'Qq': {'Qq'},
    'proofwidgets': {'ProofWidgets'},
    'plausible': {'Plausible'},
    'LeanSearchClient': {'LeanSearchClient'},
    'importGraph': {'ImportGraph'},
    'Cli': {'Cli'},
}


class _Uncacheable(Exception):
    pass


class _Snapshot(dict):
    """File evidence plus the path-resolution decisions used for this walk."""

    def __init__(self):
        super().__init__()
        self.resolutions = {}
        self.namespace_paths = {}


def _hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _stat(path):
    try:
        stat = path.stat()
    except FileNotFoundError:
        return None
    if not stat_mode.S_ISREG(stat.st_mode):
        raise _Uncacheable('dependency is not a regular file')
    return (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)


def _atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=path.parent,
                                         prefix='.' + path.name + '-', delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(value, stream, sort_keys=True, separators=(',', ':'))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def _read_json(path):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return None


class CompilationCache:
    """
    Session-scoped cache for AST/proof modules, never requirements wrappers.

    ``compile(source, output, command, run_callback, extra_dependencies=())``
    returns True on a validated hit, False after running the compiler. The
    callback receives the command list and must raise on failure (a returned
    CompletedProcess with a nonzero returncode is also rejected). ``last_reason``
    describes misses/bypasses without exposing environment values.
    """

    def __init__(self, environment, parse_imports_callback, cache_dir):
        self.environment = dict(environment)
        self.parse_imports = parse_imports_callback
        self.directory = Path(cache_dir).resolve()
        self.cwd = Path.cwd().resolve()
        self.frontend = Path(__file__).resolve().parent.parent
        self.disabled = self.environment.get('FORMALSW_NO_CACHE', '').lower() not in ('', '0', 'false', 'no')
        self.last_reason = 'not checked'
        self._parsed = {}
        self._digests = {}
        self._dirty = False
        saved = _read_json(self.directory / 'digests.json')
        if isinstance(saved, dict) and saved.get('schema') == _SCHEMA and isinstance(saved.get('files'), dict):
            self._digests = saved['files']
        self.sysroot = None
        self.search_roots = []
        if not self.disabled:
            try:
                prefix = self.environment.get('LEAN_SYSROOT')
                if not prefix:
                    lean = shutil.which('lean', path=self.environment.get('PATH'))
                    if lean is None:
                        raise _Uncacheable('Lean executable is unavailable')
                    result = subprocess.run([lean, '--print-prefix'], env=self.environment,
                                            cwd=self.cwd, text=True, capture_output=True, timeout=15)
                    if result.returncode:
                        raise _Uncacheable('Lean sysroot discovery failed')
                    prefix = result.stdout.strip()
                if not prefix:
                    raise _Uncacheable('Lean sysroot is unavailable')
                self.sysroot = self._absolute(prefix)
                # Match Lean.initSearchPath: LEAN_PATH entries precede the builtin library.
                self.search_roots = [self._absolute(path) for path in
                                     self.environment.get('LEAN_PATH', '').split(os.pathsep) if path]
                self.search_roots.append(self.sysroot / 'lib' / 'lean')
            except (OSError, subprocess.SubprocessError, _Uncacheable) as error:
                self.last_reason = str(error)

    def _absolute(self, path):
        path = Path(path)
        return (path if path.is_absolute() else self.cwd / path).absolute()

    def _digest(self, path, observed, *, force=False):
        path = self._absolute(path)
        before = _stat(path)
        if before is None:
            raise _Uncacheable('dependency is missing')
        key = str(path)
        prior = self._digests.get(key)
        if (not force and isinstance(prior, dict) and prior.get('stat') == list(before)
                and isinstance(prior.get('sha256'), str) and len(prior['sha256']) == 64):
            digest = prior['sha256']
        else:
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            self._digests[key] = {'stat': list(before), 'sha256': digest}
            self._dirty = True
        if _stat(path) != before:
            raise _Uncacheable('dependency changed while being read')
        observed[key] = before
        return digest

    @staticmethod
    def _stable(observed):
        try:
            return (all(_stat(Path(path)) == prior for path, prior in observed.items())
                    and all(Path(path).resolve() == resolved
                            for path, resolved in getattr(observed, 'resolutions', {}).items())
                    and all(CompilationCache._namespace_state(Path(path)) == prior
                            for path, prior in getattr(observed, 'namespace_paths', {}).items()))
        except (OSError, _Uncacheable):
            return False

    @staticmethod
    def _namespace_state(path):
        try:
            return stat_mode.S_IFMT(path.stat().st_mode)
        except FileNotFoundError:
            return None

    @staticmethod
    def _resolved(path, observed):
        key = str(path)
        if key not in observed.resolutions:
            observed.resolutions[key] = path.resolve()
        return observed.resolutions[key]

    def _resolve_import(self, parts, observed):
        if not parts or any(not isinstance(part, str) or not part or '/' in part or '\\' in part
                            or part in ('.', '..') for part in parts):
            raise _Uncacheable('invalid import components')
        for root in self.search_roots:
            # Lean chooses a namespace root first, without falling through when
            # a submodule is absent in that chosen root.
            namespace = root / parts[0]
            top_module = Path(str(namespace) + '.olean')
            for path in (namespace, top_module):
                key = str(path)
                if key not in observed.namespace_paths:
                    observed.namespace_paths[key] = self._namespace_state(path)
            if (observed.namespace_paths[str(namespace)] == stat_mode.S_IFDIR
                    or observed.namespace_paths[str(top_module)] is not None):
                artifact = Path(str(root.joinpath(*parts)) + '.olean')
                if _stat(artifact) is None:
                    raise _Uncacheable('import is missing in the selected namespace root')
                return root, artifact
        raise _Uncacheable('import cannot be resolved')

    def _source_for_import(self, root, parts, observed, system_library):
        root_parts = root.parts
        marker = ('.lake', 'build', 'lib', 'lean')
        package = None
        if len(root_parts) >= 4 and tuple(root_parts[-4:]) == marker:
            package = root.parents[3]
            source = Path(str(package.joinpath(*parts)) + '.lean')
        elif self._resolved(root, observed) == system_library:
            package = system_library.parent.parent
            candidates = [Path(str(base.joinpath('src', 'lean', subdir, *parts)) + '.lean')
                          for base in (package, self.sysroot) for subdir in ('lake', '')]
            source = next((candidate for candidate in candidates if candidate.is_file()), candidates[-1])
        else:
            source = Path(str(root.joinpath(*parts)) + '.lean')
        if not source.is_file():
            raise _Uncacheable('imported source cannot be located')
        return source, package

    def _trusted_library(self, source, package, parts, observed, compiler_roots):
        if (package is not None and package.parent.name == 'packages'
                and package.parent.parent.name == '.lake'
                and parts[0] in _LIBRARIES.get(package.name, set())):
            return True
        resolved = self._resolved(source, observed)
        if any(resolved.is_relative_to(root) for root in compiler_roots):
            return True
        return resolved.is_relative_to(self.frontend) and parts[0] in ('FormalSW', 'lang')

    @staticmethod
    def _without_import_lines(text, imports):
        # Mask only complete, standalone commands confirmed by Lean's header
        # parser. Executable Lean.Elab code and same-line commands remain visible.
        commands = set()
        for parts in imports:
            name = '.'.join(part if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part)
                            else '«' + part + '»' for part in parts)
            for qualifier in ('', 'public ', 'private '):
                for mode in ('', 'all '):
                    commands.add(qualifier + 'import ' + mode + name)
        return '\n'.join('' if line.strip().split('--', 1)[0].rstrip() in commands else line
                         for line in text.splitlines())

    @staticmethod
    def _includes(source, text):
        included = []
        for occurrence in _INCLUDE.finditer(text):
            literal = _LITERAL.match(text, occurrence.end())
            if literal is None:
                raise _Uncacheable('include path is not a recognized literal')
            try:
                name = json.loads(literal[1])
            except ValueError as error:
                raise _Uncacheable('include path has unsupported escaping') from error
            included.append(source.parent / name)
        return included

    def _artifact_files(self, artifact, observed, dependencies):
        # The private/server companions can contain declarations used while
        # elaborating downstream modules in Lean 4.30. Track absence as well.
        for path in (artifact, Path(str(artifact) + '.private'), Path(str(artifact) + '.server'),
                     artifact.with_suffix('.ir'), artifact.with_suffix('.so')):
            if _stat(path) is not None:
                dependencies[str(path)] = self._digest(path, observed)
            else:
                observed[str(path)] = None
                dependencies[str(path)] = None

    def _fingerprint(self, source, command, extra_dependencies):
        if self.sysroot is None:
            raise _Uncacheable('Lean sysroot is unavailable')
        if any(str(arg).startswith(('--plugin', '--load-dynlib', '--run', '--server')) for arg in command[1:]):
            raise _Uncacheable('compiler invocation has additional execution inputs')
        observed, dependencies = _Snapshot(), {}
        system_library = self._resolved(self.sysroot / 'lib' / 'lean', observed)
        compiler_roots = tuple(self._resolved(root, observed) for root in
                               (self.sysroot / 'src' / 'lean', system_library.parent.parent / 'src' / 'lean'))
        executable = shutil.which(str(command[0]), path=self.environment.get('PATH'))
        if executable is None:
            raise _Uncacheable('compiler executable cannot be resolved')
        binaries = [Path(executable), self.sysroot / 'bin' / 'lean', Path(sys.executable),
                    system_library.parent.parent / 'bin' / 'lean']
        if self.environment.get('FORMALSW_PYTHON'):
            python = shutil.which(self.environment['FORMALSW_PYTHON'], path=self.environment.get('PATH'))
            if python is None:
                raise _Uncacheable('quotation Python executable cannot be resolved')
            binaries.append(Path(python))
        for path in binaries:
            dependencies[str(path)] = self._digest(path, observed)
        # The executable can be a small loader: shared compiler/runtime code
        # is part of the toolchain identity too.
        for root in {self.sysroot, system_library.parent.parent}:
            for directory in (root / 'lib', root / 'lib' / 'lean'):
                for path in sorted(directory.glob('*')):
                    if path.is_file() and any(extension in path.name for extension in ('.so', '.dylib', '.dll')):
                        dependencies[str(path)] = self._digest(path, observed)
        # Quotation elaboration may invoke Python even when Lean objects did
        # not change. Include the launcher and all runtime frontend modules.
        frontend_sources = [self.frontend / 'formalsw'] + sorted((self.frontend / 'lang').rglob('*.py'))
        for path in frontend_sources:
            dependencies[str(path)] = self._digest(path, observed)
        for path in extra_dependencies:
            path = self._absolute(path)
            dependencies[str(path)] = self._digest(path, observed)
        visited, visiting, imports_seen = set(), set(), {}

        def visit(path, trusted=False):
            path = self._absolute(path)
            if path in visiting:
                raise _Uncacheable('cyclic Lean imports')
            if path in visited:
                return
            visiting.add(path)
            digest = self._digest(path, observed)
            dependencies[str(path)] = digest
            contents = path.read_bytes()
            if hashlib.sha256(contents).hexdigest() != digest:
                raise _Uncacheable('dependency changed before parsing imports')
            text = contents.decode('utf-8')
            key = (str(path), digest)
            if key not in self._parsed:
                self._parsed[key] = tuple(tuple(parts) for parts in self.parse_imports(text))
            imports = self._parsed[key]
            if not trusted:
                body = self._without_import_lines(text, imports)
                if _EFFECTS.search(body):
                    raise _Uncacheable(f'project source has compile-time effects: {path}')
                for included in self._includes(path, body):
                    included = self._absolute(included)
                    dependencies[str(included)] = self._digest(included, observed)
            # Lean's parser callback includes implicit Init. Keep this fallback
            # for lightweight callers, without imposing Init on prelude files.
            if not re.search(r'(?m)^\s*prelude\b', text) and ('Init',) not in imports:
                imports = (('Init',), *imports)
            for parts in imports:
                if parts in imports_seen:
                    if imports_seen[parts] in visiting:
                        raise _Uncacheable('cyclic Lean imports')
                    continue
                root, artifact = self._resolve_import(parts, observed)
                self._artifact_files(artifact, observed, dependencies)
                imported, package = self._source_for_import(root, parts, observed, system_library)
                imports_seen[parts] = self._absolute(imported)
                visit(imported, self._trusted_library(imported, package, parts, observed, compiler_roots))
            visiting.remove(path)
            visited.add(path)

        visit(source)
        if not self._stable(observed):
            raise _Uncacheable('inputs changed while computing the fingerprint')
        fingerprint = _hash({'schema': _SCHEMA, 'cwd': str(self.cwd), 'source': str(source),
                             'command': list(map(str, command)), 'dependencies': dependencies,
                             'resolved_paths': {key: str(path) for key, path in observed.resolutions.items()},
                             'environment': _hash(self.environment), 'python': sys.version})
        return fingerprint, observed

    def _outputs(self, output):
        observed, digests = {}, {}
        if not output.is_file():
            raise _Uncacheable('compiled output is missing')
        for path in (output, Path(str(output) + '.private'), Path(str(output) + '.server'),
                     output.with_suffix('.ir'), output.with_suffix('.so')):
            if path.is_file():
                # Always hash cached outputs; metadata alone is not evidence
                # that a proof object has remained intact.
                digests[str(path)] = self._digest(path, observed, force=True)
            else:
                observed[str(path)] = None
                digests[str(path)] = None
        return digests, observed

    def _run(self, command, callback):
        result = callback(command)
        if getattr(result, 'returncode', 0):
            raise subprocess.CalledProcessError(result.returncode, command,
                                                output=getattr(result, 'stdout', None),
                                                stderr=getattr(result, 'stderr', None))

    def compile(self, source, output, command, run_callback, extra_dependencies=()):
        source, output = self._absolute(source), self._absolute(output)
        command = list(command)
        record = self.directory / (_hash(str(output)) + '.json')
        before = None
        self.last_reason = 'cache disabled' if self.disabled else 'cache miss'
        if not self.disabled and not source.name.endswith('.reqs.lean'):
            try:
                before, observed = self._fingerprint(source, command, extra_dependencies)
                saved = _read_json(record)
                if isinstance(saved, dict) and saved.get('schema') == _SCHEMA and saved.get('input') == before:
                    outputs, output_stats = self._outputs(output)
                    if saved.get('outputs') == outputs and self._stable(observed) and self._stable(output_stats):
                        self.last_reason = 'cache hit'
                        return True
            except (OSError, ValueError, TypeError, _Uncacheable) as error:
                self.last_reason = str(error)
                before = None
        elif source.name.endswith('.reqs.lean'):
            self.last_reason = 'requirements are always checked freshly'
        # An unsuccessful replacement must not leave an old success record
        # available to a later invocation.
        try:
            record.unlink(missing_ok=True)
        except OSError:
            before = None
        self._run(command, run_callback)
        if before is not None:
            try:
                after, observed = self._fingerprint(source, command, extra_dependencies)
                outputs, output_stats = self._outputs(output)
                if after == before and self._stable(observed) and self._stable(output_stats):
                    _atomic_json(record, {'schema': _SCHEMA, 'input': after, 'outputs': outputs})
                else:
                    self.last_reason = 'inputs changed during compilation'
            except (OSError, ValueError, TypeError, _Uncacheable) as error:
                self.last_reason = str(error)
        if self._dirty:
            try:
                _atomic_json(self.directory / 'digests.json', {'schema': _SCHEMA, 'files': self._digests})
                self._dirty = False
            except OSError:
                pass  # A cache write failure never substitutes for checking.
        return False
