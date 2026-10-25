"""Fetch and precompile this repository's pinned dependencies.

Each dependency is a git repository at a pinned commit. It is checked out
into `.cache/deps/NAME` and its packages are precompiled, in the order of
DEPS, into the build directory (or its kernel subdirectory for test-only
packages). Library consumers use `-I build`. The script never touches a
local checkout of a dependency, which may hold someone's unrelated work.

Consistency: every repository pins all of its transitive dependencies, and
its pins must equal those of the repositories it depends on. After fetching
a dependency, this script reads that repository's own `scripts/deps.py` and
fails if any shared dependency is pinned at a different commit.

A dependency with `commit=None` is declared but not yet pinned; it is
skipped with a notice. A dependency with `test_only=True` is built for the
tests but may not be imported by `src/` (scripts/packages.py's graph does not
list it). Test-only dependencies come from an optional kernel suite's
`tests/kernel/deps.json` and are excluded by default. With --with-tests, their
packages and stamps go in OUTPUT/kernel, separate from the library packages.

Use --tests-only after the library build to prepare kernel packages without
rebuilding public dependencies. All preparation commands take the library build
lock so they cannot replace packages used by running tests.
"""
import argparse
import ast
from pathlib import Path
import subprocess

from build_state import build_lock, compiler_identity, validate
from packages import test_dependencies

ROOT = Path(__file__).resolve().parent.parent
DEPS = {
    'apn_mojo': dict(url='https://github.com/Spellbound-Mojo/apn_mojo.git', commit='71d54e0f3c6bb1139f51db12885a6cd6a8cc2886', packages=['src/apn_mojo']),
}
DEPS.update(test_dependencies())


def git(*args, cwd):
    return subprocess.run(['git', *args], cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


def checkout(name, spec):
    """The pinned source tree of a dependency, fetched once."""
    folder = ROOT / '.cache' / 'deps' / name
    if (folder / '.git').is_dir() and git('rev-parse', 'HEAD', cwd=folder) == spec['commit']:
        return folder
    folder.mkdir(parents=True, exist_ok=True)
    if not (folder / '.git').is_dir():
        git('init', '-q', cwd=folder)
        git('remote', 'add', 'origin', spec['url'], cwd=folder)
    git('fetch', '-q', '--depth', '1', 'origin', spec['commit'], cwd=folder)
    git('checkout', '-q', '--detach', 'FETCH_HEAD', cwd=folder)
    return folder


def pins_of(folder):
    """The commits a dependency pins, read from its scripts/deps.py without running it."""
    path = folder / 'scripts' / 'deps.py'
    if not path.is_file():
        return {}
    pins = {}
    for node in ast.walk(ast.parse(path.read_text())):
        if isinstance(node, ast.Assign) and any(getattr(t, 'id', None) == 'DEPS' for t in node.targets):
            for key, value in zip(node.value.keys, node.value.values):
                if isinstance(key, ast.Constant) and isinstance(value, ast.Call):
                    for keyword in value.keywords:
                        if keyword.arg == 'commit' and isinstance(keyword.value, ast.Constant):
                            pins[key.value] = keyword.value.value
    return pins


def precompile(name, spec, folder, output, extra=()):
    """Reuse packages only when both their source commit and compiler match."""
    stamp = output / f'{name}.commit'
    compiler_stamp = output / f'{name}.compiler'
    compiler = compiler_identity()
    targets = [output / f'{Path(p).name}.mojoc' for p in spec['packages']]
    if (stamp.is_file() and stamp.read_text().strip() == spec['commit']
            and compiler_stamp.is_file() and compiler_stamp.read_text().strip() == compiler
            and all(t.is_file() for t in targets)):
        return
    # A failed or interrupted rebuild must not leave a reusable cache stamp.
    stamp.unlink(missing_ok=True)
    compiler_stamp.unlink(missing_ok=True)
    for package, target in zip(spec['packages'], targets):
        cmd = ['mojo', 'precompile', '-I', str(output), *extra, str(folder / package), '-o', str(target)]
        print(' '.join(cmd), flush=True)
        subprocess.run(cmd, cwd=ROOT, check=True)
    stamp.write_text(spec['commit'] + '\n')
    compiler_stamp.write_text(compiler + '\n')


def prepare(output, *, with_tests=False, tests_only=False):
    """Build library dependencies, optionally adding isolated kernel test packages."""
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    problems = []
    for name, spec in DEPS.items():
        test_only = spec.get('test_only', False)
        if tests_only and not test_only:
            continue
        if test_only and not (with_tests or tests_only):
            continue
        if spec['commit'] is None:
            print(f'{name}: not pinned yet; skipped')
            continue
        folder = checkout(name, spec)
        for shared, commit in pins_of(folder).items():
            if shared in DEPS and DEPS[shared]['commit'] not in (None, commit):
                problems.append(f'{name} pins {shared} at {commit[:12]}, this repository at {DEPS[shared]["commit"][:12]}')
        destination = output / 'kernel' if test_only else output
        destination.mkdir(parents=True, exist_ok=True)
        extra = ('-I', str(output)) if test_only else ()
        precompile(name, spec, folder, destination, extra)
        print(f'{name} at {spec["commit"][:12]}: ok')
    if problems:
        print('inconsistent pins:\n  ' + '\n  '.join(problems))
        return 1
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='build', help='Directory for the library .mojoc files')
    parser.add_argument('--with-tests', action='store_true', help='Also build test-only dependencies in OUTPUT/kernel')
    parser.add_argument('--tests-only', action='store_true', help='Prepare only kernel packages for the existing library build')
    args = parser.parse_args()
    with build_lock(ROOT / args.output, exclusive=True) as output:
        if not args.tests_only:
            return prepare(output, with_tests=args.with_tests)
        snapshot = validate(output)
        kernel = output / 'kernel'
        kernel.mkdir(exist_ok=True)
        stamp = kernel / 'library-build-id'
        previous = stamp.read_text().strip() if stamp.is_file() else None
        stamp.unlink(missing_ok=True)
        if previous != snapshot.identity:
            for name, spec in DEPS.items():
                if spec.get('test_only'):
                    (kernel / f'{name}.commit').unlink(missing_ok=True)
        result = prepare(output, tests_only=True)
        if result == 0:
            stamp.write_text(snapshot.identity + '\n')
        return result


if __name__ == '__main__':
    raise SystemExit(main())
