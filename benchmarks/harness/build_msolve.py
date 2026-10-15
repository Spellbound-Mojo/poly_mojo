"""Build the pinned msolve release from source with the environment's libraries.

msolve is not packaged on conda-forge. This script clones the tagged release,
checks the commit, and installs it under .cache/opt/msolve with msolve's own
default optimization flags; the harness then calls that binary. Run it through
`pixi run msolve-build` so GMP, MPFR, FLINT, and autotools come from the pinned
environment.
"""
import os
import subprocess
import sys
from pathlib import Path

TAG = 'v0.11.0'
COMMIT = 'cc044551f8e202d00691990fd3fd0b1226a88ea2'
URL = 'https://github.com/algebraic-solving/msolve.git'
HERE = Path(__file__).resolve().parent.parent
SOURCE = HERE / '.cache' / 'src' / f'msolve-{TAG}'
PREFIX = HERE / '.cache' / 'opt' / 'msolve'


def run(*cmd, cwd, env=None):
    print('+', ' '.join(map(str, cmd)), flush=True)
    subprocess.run(list(map(str, cmd)), cwd=cwd, env=env, check=True)


def main():
    binary = PREFIX / 'bin' / 'msolve'
    if binary.is_file() and '--force' not in sys.argv:
        print(f'msolve already built: {binary}')
        return 0
    if not SOURCE.is_dir():
        SOURCE.parent.mkdir(parents=True, exist_ok=True)
        run('git', 'clone', '--quiet', '--depth', '1', '--branch', TAG, URL, SOURCE, cwd=HERE)
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=SOURCE, capture_output=True, text=True, check=True).stdout.strip()
    if head != COMMIT:
        raise SystemExit(f'msolve {TAG} resolved to {head}, expected {COMMIT}')
    prefix = os.environ.get('CONDA_PREFIX') or os.environ.get('PIXI_PROJECT_ROOT')
    if not prefix:
        raise SystemExit('Run this script through `pixi run msolve-build`.')
    env = dict(os.environ)
    env['CPPFLAGS'] = f'-I{prefix}/include'
    env['LDFLAGS'] = f'-L{prefix}/lib -Wl,-rpath,{prefix}/lib'
    run('./autogen.sh', cwd=SOURCE, env=env)
    run('./configure', f'--prefix={PREFIX}', cwd=SOURCE, env=env)
    run('make', f'-j{os.cpu_count() or 1}', cwd=SOURCE, env=env)
    run('make', 'install', cwd=SOURCE, env=env)
    print(f'msolve installed: {binary}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
