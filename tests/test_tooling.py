"""Dependency and test boundaries for standalone library builds."""
import contextlib
import io
import json
import fcntl
import threading
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib
import unittest
from unittest.mock import patch
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import deps
import suite
import packages
import build as library_builder
import build_state
import check_docstrings
import check_array_api
import verify_docs_examples
import compiler_diagnostics
import test_executable
import check_rejections


# A stand-in for the optional kernel suite's test-only dependency.
TEST_ONLY = dict(url='https://example.invalid/kernel.git', commit='0' * 40,
                 packages=['src/kernel_terms', 'src/kernel_checks'], test_only=True)


def with_test_dependency():
    return patch.dict(deps.DEPS, {'apn_mojo': deps.DEPS['apn_mojo'], 'kernel': TEST_ONLY}, clear=True)


class DependencyTests(unittest.TestCase):
    def test_test_dependencies_come_only_from_the_kernel_suite(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            self.assertEqual(packages.test_dependencies(root), {})
            declared = root / packages.TEST_DEPS
            declared.parent.mkdir(parents=True)
            declared.write_text(json.dumps({'kernel': {k: v for k, v in TEST_ONLY.items() if k != 'test_only'}}))
            self.assertEqual(packages.test_dependencies(root), {'kernel': TEST_ONLY})

    def test_default_never_accesses_private_dependency(self):
        def public_only(name, spec):
            if spec.get('test_only'):
                raise AssertionError('library build attempted a private checkout')
            return Path('/public') / name

        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder).resolve() / 'build'
            with with_test_dependency(), \
                    patch.object(deps, 'checkout', side_effect=public_only) as checkout, \
                    patch.object(deps, 'pins_of', return_value={}), \
                    patch.object(deps, 'precompile') as precompile, \
                    patch.object(sys, 'argv', ['deps.py', '--output', str(output)]), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(deps.main(), 0)
            self.assertEqual([c.args[0] for c in checkout.call_args_list], ['apn_mojo'])
            self.assertEqual(precompile.call_args.args[3], output)
            self.assertFalse((output / 'kernel').exists())

    def test_test_dependencies_require_opt_in_and_separate_output(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder).resolve() / 'build'
            with with_test_dependency(), \
                    patch.object(deps, 'checkout', side_effect=lambda name, spec: Path('/sources') / name) as checkout, \
                    patch.object(deps, 'pins_of', return_value={}), \
                    patch.object(deps, 'precompile') as precompile, \
                    patch.object(sys, 'argv', ['deps.py', '--output', str(output), '--with-tests']), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(deps.main(), 0)
            self.assertEqual([c.args[0] for c in checkout.call_args_list], ['apn_mojo', 'kernel'])
            self.assertEqual([c.args[3] for c in precompile.call_args_list], [output, output / 'kernel'])
            self.assertEqual(precompile.call_args.args[4], ('-I', str(output)))

    def test_kernel_compilation_uses_both_include_directories(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder)
            kernel = output / 'kernel'
            kernel.mkdir()
            spec = TEST_ONLY
            with patch.object(deps.subprocess, 'run') as run, \
                    patch.object(deps, 'compiler_identity', return_value='Mojo test toolchain'), \
                    contextlib.redirect_stdout(io.StringIO()):
                deps.precompile('kernel', spec, Path('/sources/kernel'), kernel, ('-I', str(output)))
            for compiled, source in zip(run.call_args_list, spec['packages'], strict=True):
                command = compiled.args[0]
                self.assertEqual(command[2:6], ['-I', str(kernel), '-I', str(output)])
                self.assertEqual(command[-1], str(kernel / f'{Path(source).name}.mojoc'))
            self.assertEqual((kernel / 'kernel.commit').read_text(), spec['commit'] + '\n')

    def test_dependency_rebuilds_after_compiler_upgrade_and_then_reuses(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder)
            spec = dict(commit='pinned-source', packages=['src/dependency'])
            (output / 'dependency.commit').write_text(spec['commit'] + '\n')
            (output / 'dependency.mojoc').write_bytes(b'legacy cached package')

            def compile_package(command, **kwargs):
                Path(command[-1]).write_bytes(b'compiled package')

            with patch.object(deps, 'compiler_identity', return_value='Mojo 1.1.0') as identity, \
                    patch.object(deps.subprocess, 'run', side_effect=compile_package) as compile_, \
                    contextlib.redirect_stdout(io.StringIO()):
                # A legacy cache without compiler provenance must be rebuilt.
                deps.precompile('dependency', spec, Path('/source'), output)
                self.assertEqual(compile_.call_count, 1)
                deps.precompile('dependency', spec, Path('/source'), output)
                self.assertEqual(compile_.call_count, 1)
                identity.return_value = 'Mojo 1.2.0'
                deps.precompile('dependency', spec, Path('/source'), output)
                self.assertEqual(compile_.call_count, 2)
                deps.precompile('dependency', spec, Path('/source'), output)
                self.assertEqual(compile_.call_count, 2)

    def test_failed_dependency_upgrade_invalidates_cache(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder)
            spec = dict(commit='pinned-source', packages=['src/dependency'])
            (output / 'dependency.commit').write_text(spec['commit'] + '\n')
            (output / 'dependency.compiler').write_text('Mojo 1.1.0\n')
            (output / 'dependency.mojoc').write_bytes(b'old package')
            with patch.object(deps, 'compiler_identity', return_value='Mojo 1.2.0'), \
                    patch.object(deps.subprocess, 'run', side_effect=subprocess.CalledProcessError(1, 'mojo')), \
                    contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(subprocess.CalledProcessError):
                    deps.precompile('dependency', spec, Path('/source'), output)
            self.assertFalse((output / 'dependency.commit').exists())
            self.assertFalse((output / 'dependency.compiler').exists())


def fake_executable():
    return SimpleNamespace(binary=Path('/compiled-suite'), reused=True, programs=(),
                           record={'inputs': {'sources': {}}}, report=lambda: {})


class TestSelectionTests(unittest.TestCase):
    def run_selection(self, extra, flags=('-O0',)):
        fixtures = [
            ('library', ROOT / 'tests/polynomials/test_dense.mojo', None, ()),
            ('kernel', ROOT / 'tests/kernel/test_crosscheck.mojo', None, ()),
        ]
        snapshot = build_state.LibraryBuild(Path('build'), dict(build_id='one-build', compiler='test', artifacts={}))
        def execute(job, *_):
            return dict(name=job[0], passed=True, detail='', seconds=0)
        with tempfile.TemporaryDirectory() as folder, \
                patch.object(suite, 'prepared_build', return_value=contextlib.nullcontext(snapshot)), \
                patch.object(suite, 'jobs', return_value=fixtures), \
                patch.object(suite, 'prepare', return_value=fake_executable()) as compiled, \
                patch.object(suite, 'source_inputs', return_value={}), \
                patch.object(suite, '_run', side_effect=execute) as run, \
                patch.object(sys, 'argv', ['suite.py', '--batches', '1', '--jobs', '1', '--report', str(Path(folder) / 'report.json'), *extra]), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(suite.main(), 0)
        self.assertEqual(compiled.call_count, 1)
        self.assertEqual(compiled.call_args.kwargs['flags'], flags)
        return [c.args[0][0] for c in run.call_args_list], compiled.call_args

    def test_library_mode_excludes_kernel_and_rejections(self):
        selected, built = self.run_selection(['--library-only'])
        self.assertEqual(selected, ['library'])
        self.assertFalse(built.kwargs['kernel'])
        self.assertEqual(built.kwargs['compiler_threads'], 1)

    def test_explicit_optimization_and_compiler_threads(self):
        selected, built = self.run_selection(
            ['--library-only', '--optimization', '3', '--compiler-threads', '1'], flags=('-O3',))
        self.assertEqual(selected, ['library'])
        self.assertEqual(built.kwargs['compiler_threads'], 1)

    def test_release_mode_keeps_kernel_coverage(self):
        selected, built = self.run_selection([])
        self.assertCountEqual(selected, ['library', 'kernel'])
        self.assertTrue(built.kwargs['kernel'])

    def test_path_filter_selects_execution_without_changing_suite(self):
        selected, built = self.run_selection(['library'])
        self.assertEqual(selected, ['library'])
        self.assertEqual(len(built.args[0]), 2)

    def test_kernel_only_uses_its_own_complete_suite(self):
        selected, built = self.run_selection(['--kernel-only'])
        self.assertEqual(selected, ['kernel'])
        self.assertEqual(len(built.args[0]), 1)


    def test_rejection_checks_require_failure_and_matching_diagnostic(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            path = root / 'tests/compile_fail/example.mojo'
            path.parent.mkdir(parents=True)
            path.write_text('# expect: expected failure\n')
            snapshot = SimpleNamespace(path=root / 'build')
            for code, diagnostic, passed in [(1, 'expected failure', True),
                                             (0, 'expected failure', False),
                                             (1, 'different failure', False),
                                             (None, 'expected failure', False)]:
                with self.subTest(code=code, diagnostic=diagnostic), \
                        patch.object(check_rejections, 'ROOT', root), \
                        patch.object(check_rejections, 'run', return_value=dict(
                            returncode=code, stdout='', stderr=diagnostic, seconds=0)):
                    self.assertEqual(check_rejections.check(path, snapshot, 1)['passed'], passed)



class BatchTests(unittest.TestCase):
    def test_balanced_batches_cover_each_configuration_once(self):
        fixtures = [(str(i), ROOT / f'tests/test_{i}.mojo', None, ()) for i in range(9)]
        fixtures += [(str(i) + ' variant', path, None, ('-D', 'VARIANT=1'))
                     for i, (_, path, _, _) in enumerate(fixtures[:3])]
        groups = suite.batches(list(reversed(fixtures)), 4)
        self.assertEqual(groups, suite.batches(fixtures, 4))
        plain = [group for flags, group in groups if not flags]
        self.assertEqual([len(group) for group in plain], [3, 2, 2, 2])
        self.assertEqual([job[0] for job in plain[0]], ['0', '4', '8'])
        self.assertCountEqual([job for _, group in groups for job in group], fixtures)
        for flags, group in groups:
            self.assertTrue(group)
            self.assertTrue(all(job[3] == flags for job in group))
        self.assertEqual(suite.batches([], 4), [])
        with self.assertRaisesRegex(ValueError, 'must be positive'):
            suite.batches(fixtures, 0)

    def run_batches(self, *, fail_compile=False, fail_runtime=False):
        fixtures = [(str(i), ROOT / f'tests/test_{i}.mojo', None, ()) for i in range(8)]
        snapshot = build_state.LibraryBuild(Path('build'), dict(build_id='one-build', compiler='test', artifacts={}))
        events = []

        def prepare(paths, *_args, **_kwargs):
            events.append(('build', [path.stem for path in paths]))
            if fail_compile and paths[0] == fixtures[1][1]:
                raise suite.CompilationFailed({'compile': {'returncode': -9, 'stderr': ''}})
            return fake_executable()

        def execute(job, *_):
            events.append(('run', job[0]))
            return dict(name=job[0], passed=not (fail_runtime and job[0] == '0'), detail='', seconds=0)

        with tempfile.TemporaryDirectory() as folder:
            report = Path(folder) / 'report.json'
            with patch.object(suite, 'prepared_build', return_value=contextlib.nullcontext(snapshot)), \
                    patch.object(suite, 'jobs', return_value=fixtures), \
                    patch.object(suite, 'prepare', side_effect=prepare), \
                    patch.object(suite, 'source_inputs', return_value={}), \
                    patch.object(suite, '_run', side_effect=execute), \
                    patch.object(sys, 'argv', ['suite.py', '--jobs', '1', '--report', str(report)]), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                status = suite.main()
            return status, events, json.loads(report.read_text())

    def test_each_batch_finishes_before_the_next_build(self):
        status, events, report = self.run_batches()
        expected = []
        for i in range(4):
            expected += [('build', [f'test_{i}', f'test_{i + 4}']), ('run', str(i)), ('run', str(i + 4))]
        self.assertEqual(events, expected)
        self.assertEqual(status, 0)
        self.assertTrue(report['complete'] and report['passed'])
        self.assertEqual(len(report['records']), 8)
        self.assertEqual(len(report['executables']), 4)

    def test_later_compile_failure_keeps_finished_batch_results(self):
        status, events, report = self.run_batches(fail_compile=True)
        self.assertEqual(status, 1)
        self.assertEqual(len(events), 4)
        self.assertEqual([r['name'] for r in report['records']], ['0', '4'])
        self.assertTrue(report['complete'])
        self.assertFalse(report['passed'])
        self.assertEqual(report['total'], 8)
        self.assertEqual(report['compile_error']['compile']['returncode'], -9)

    def test_runtime_failure_does_not_hide_remaining_batches(self):
        status, _, report = self.run_batches(fail_runtime=True)
        self.assertEqual(status, 1)
        self.assertTrue(report['complete'])
        self.assertFalse(report['passed'])
        self.assertEqual(len(report['records']), 8)
        self.assertEqual(len(report['executables']), 4)


class TaskGraphTests(unittest.TestCase):
    def test_public_tasks_do_not_fetch_test_dependencies(self):
        tasks = tomllib.loads((ROOT / 'pixi.toml').read_text())['tasks']

        def dependencies(task):
            found = set()
            pending = [task]
            while pending:
                current = pending.pop()
                if current not in found:
                    found.add(current)
                    pending.extend(tasks[current].get('depends-on', []))
            return found

        for task in ('test-library', 'test-api', 'test-rejections', 'docs-test', 'docstrings'):
            self.assertFalse(dependencies(task) & {'build', 'deps'}, task)
        self.assertEqual(dependencies('build'), {'build', 'deps'})
        for task in tasks:
            self.assertNotIn('--with-tests', tasks[task].get('cmd', ''), task)
            self.assertNotIn('--tests-only', tasks[task].get('cmd', ''), task)


class ArrayPackageTests(unittest.TestCase):
    def test_namespace_exports_ignore_comments_and_strings(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            package = root / 'src/poly'
            package.mkdir(parents=True)
            (package / '__init__.mojo').write_text(
                '\"\"\"Example: from . import hidden\"\"\"\n'
                '# from . import also_hidden\n'
                'from . import (dense, sparse)\n'
                'from ._common import coefficients\n'
            )
            self.assertEqual(packages.public_modules('poly', root), {
                'dense': 'src/poly/dense.mojo', 'sparse': 'src/poly/sparse.mojo',
            })
            self.assertEqual(set(packages.exports('poly', root)), {'dense', 'sparse', 'coefficients'})

    def test_regular_suite_discovers_runtime_cases_only(self):
        selected = {job[1].relative_to(ROOT).as_posix() for job in suite.jobs(None)}
        self.assertIn('tests/poly/test_boundary.mojo', selected)
        self.assertIn('tests/poly/test_operations.mojo', selected)
        self.assertNotIn('tests/compile_fail/array_dense_float.mojo', selected)
        self.assertIn('tests/compile/coefficient_buffer_borrows.mojo', selected)


class SharedBuildTests(unittest.TestCase):
    def setUp(self):
        self.stack = contextlib.ExitStack()
        self.addCleanup(self.stack.close)
        self.root = Path(self.stack.enter_context(tempfile.TemporaryDirectory())).resolve()
        self.output = self.root / 'build'
        self.output.mkdir()
        for name in ('polynomials', 'poly'):
            source = self.root / 'src' / name
            source.mkdir(parents=True)
            (source / '__init__.mojo').write_text('')
        (self.output / 'apn_mojo.mojoc').write_bytes(b'pinned dependency')
        (self.output / 'apn_mojo.commit').write_text('pinned-commit\n')
        for module in (build_state, library_builder, suite, check_array_api, verify_docs_examples, check_rejections):
            self.stack.enter_context(patch.object(module, 'ROOT', self.root))
        self.commands = []
        self.compiler_result = subprocess.CompletedProcess([], 0, '', '')
        self.stack.enter_context(patch.object(subprocess, 'run', side_effect=self.compiler))
        self.stack.enter_context(contextlib.redirect_stdout(io.StringIO()))

    def compiler(self, command, **kwargs):
        self.commands.append(command)
        if command[:2] == ['mojo', '--version']:
            return subprocess.CompletedProcess(command, 0, 'Mojo test toolchain', '')
        if command[:2] == ['mojo', 'precompile']:
            if self.compiler_result.returncode == 0:
                Path(command[command.index('-o') + 1]).write_bytes(b'compiled package')
            return self.compiler_result
        if command[:2] == ['mojo', 'build'] and any('compile_fail' in arg for arg in command):
            return subprocess.CompletedProcess(command, 1, '', 'deliberate rejection')
        if command[:2] == ['mojo', 'build']:
            Path(command[command.index('-o') + 1]).write_bytes(b'compiled runtime')
        return subprocess.CompletedProcess(command, 0, 'expected output\n', '')

    def build(self):
        library_builder.build(self.output)
        return json.loads((self.output / build_state.MANIFEST).read_text())

    def test_all_runners_use_exactly_one_precompile_per_package(self):
        record = self.build()
        tests = self.root / 'tests/poly'
        tests.mkdir(parents=True)
        test = tests / 'test_one.mojo'
        test.write_text('def main() raises:\n    pass\n')
        (tests / 'test_two.mojo').write_text(test.read_text())
        rejected = self.root / 'tests/compile_fail'
        rejected.mkdir()
        (rejected / 'array_invalid.mojo').write_text('# expect: deliberate rejection\n')
        example = 'docs/examples/one.mojo'
        (self.root / example).parent.mkdir(parents=True)
        (self.root / example).write_text('def main() raises:\n    pass\n')
        second_example = 'docs/examples/two.mojo'
        (self.root / second_example).write_text((self.root / example).read_text())
        with patch.object(sys, 'argv', ['suite.py', '--library-only', '--report', str(self.root / 'suite.json')]):
            self.assertEqual(suite.main(), 0)
        with patch.object(check_array_api, 'EXPECTED', {'test_one.mojo': 'expected output\n', 'test_two.mojo': 'expected output\n'}), \
                patch.object(sys, 'argv', ['check_array_api.py', '--output', str(self.root / 'api')]):
            self.assertEqual(check_array_api.main(), 0)
        with patch.object(verify_docs_examples, 'data', return_value={
                'examples': {example: {'stdout': 'expected output\n'}, second_example: {'stdout': 'expected output\n'}}}), \
                patch.object(sys, 'argv', ['verify_docs_examples.py', '--output', str(self.root / 'docs-results')]):
            self.assertEqual(verify_docs_examples.main(), 0)
        with patch.object(sys, 'argv', ['check_docstrings.py']):
            self.assertEqual(check_docstrings.main(), 0)
        compiles = [cmd for cmd in self.commands if cmd[:2] == ['mojo', 'precompile']]
        self.assertEqual(len(compiles), 2)
        self.assertEqual([Path(cmd[-1]).name for cmd in compiles], ['polynomials.mojoc', 'poly.mojoc'])
        for cmd in self.commands:
            if cmd[:2] in (['mojo', 'build'], ['mojo', 'run']):
                includes = [cmd[i + 1] for i, arg in enumerate(cmd) if arg == '-I']
                self.assertIn(str(self.output), includes)
                self.assertNotIn(str(self.root / 'src'), includes)
                self.assertFalse(any('/package' in include for include in includes))
        for report in ('suite.json', 'api/report.json', 'docs-results/report.json'):
            actual = json.loads((self.root / report).read_text())
            self.assertTrue(actual['passed'])
            self.assertEqual(actual['library_build']['build_id'], record['build_id'])
        self.assertEqual(len(json.loads((self.root / 'docs-results/report.json').read_text())['records']), 4)
        self.assertEqual(len(json.loads((self.root / 'api/report.json').read_text())['records']), 4)
        runtime_compiles = [cmd for cmd in self.commands if cmd[:2] == ['mojo', 'build']]
        self.assertEqual(len(runtime_compiles), 6)  # Two small runtime batches; O0/O3 for each matrix.
        self.assertFalse(any(cmd[:2] == ['mojo', 'run'] for cmd in self.commands))

    def test_four_cached_batches_and_filtered_rerun_share_one_library(self):
        self.build()
        tests = self.root / 'tests/poly'
        tests.mkdir(parents=True)
        for i in range(8):
            (tests / f'test_{i}.mojo').write_text('def main() raises:\n    pass\n')
        report = self.root / 'suite.json'
        command = ['suite.py', '--library-only', '--jobs', '1', '--report', str(report)]
        self.commands.clear()
        with patch.object(sys, 'argv', command):
            self.assertEqual(suite.main(), 0)
        full = json.loads(report.read_text())
        self.assertEqual(len(full['executables']), 4)
        self.assertEqual(len(full['records']), 8)
        self.assertEqual(sum(cmd[:2] == ['mojo', 'build'] for cmd in self.commands), 4)
        self.assertFalse(any(cmd[:2] == ['mojo', 'precompile'] for cmd in self.commands))
        self.commands.clear()
        with patch.object(sys, 'argv', [*command, 'test_3']):
            self.assertEqual(suite.main(), 0)
        filtered = json.loads(report.read_text())
        self.assertEqual(len(filtered['records']), 1)
        self.assertTrue(filtered['executables'][0]['reused'])
        self.assertEqual(filtered['executables'][0]['binary'], full['executables'][3]['binary'])
        self.assertEqual(len(filtered['executables'][0]['inputs']['programs']), 2)
        self.assertFalse(any(cmd[:2] in (['mojo', 'build'], ['mojo', 'precompile']) for cmd in self.commands))

    def test_missing_build_is_not_rebuilt(self):
        with self.assertRaisesRegex(SystemExit, 'build.*once before testing'):
            with build_state.prepared_build():
                self.fail('missing packages were accepted')
        self.assertEqual(self.commands, [])

    def test_source_edits_require_explicit_rebuild(self):
        self.build()
        self.commands.clear()
        (self.root / 'src/poly/__init__.mojo').write_text('# changed\n')
        with self.assertRaisesRegex(SystemExit, 'sources or build inputs changed'):
            with build_state.prepared_build():
                self.fail('stale package was accepted')
        self.assertEqual(self.commands, [])

    def test_test_edits_do_not_invalidate_build(self):
        record = self.build()
        (self.root / 'tests').mkdir()
        (self.root / 'tests/test.py').write_text('# a new test\n')
        with build_state.prepared_build() as snapshot:
            self.assertEqual(snapshot.identity, record['build_id'])

    def test_replaced_package_and_dependency_are_rejected(self):
        self.build()
        for name in ('poly.mojoc', 'apn_mojo.mojoc', 'apn_mojo.commit'):
            with self.subTest(name=name):
                path = self.output / name
                original = path.read_bytes()
                path.write_bytes(b'replaced')
                with self.assertRaisesRegex(SystemExit, 'package or dependency changed'):
                    with build_state.prepared_build():
                        self.fail('replaced artifact was accepted')
                path.write_bytes(original)

    def test_toolchain_changes_are_rejected(self):
        self.build()
        with patch.object(build_state, 'compiler_identity', return_value='different toolchain'):
            with self.assertRaisesRegex(SystemExit, 'toolchain changed'):
                with build_state.prepared_build():
                    self.fail('different toolchain was accepted')

    def test_failed_build_invalidates_previous_manifest(self):
        self.build()
        self.compiler_result = subprocess.CompletedProcess([], 1, '', 'compiler error')
        with self.assertRaisesRegex(SystemExit, 'compiler error'):
            library_builder.build(self.output)
        self.assertFalse((self.output / build_state.MANIFEST).exists())

    def test_non_documentation_warnings_still_fail_build(self):
        self.compiler_result = subprocess.CompletedProcess([], 0, '', 'warning: deprecated operation')
        with self.assertRaisesRegex(SystemExit, 'deprecated operation'):
            self.build()
        self.assertFalse((self.output / build_state.MANIFEST).exists())

    def test_docstring_gate_reuses_recorded_diagnostics(self):
        (self.root / 'src/poly/__init__.mojo').write_text('# authored declaration\n')
        self.compiler_result = subprocess.CompletedProcess([], 0, '',
            "src/poly/__init__.mojo:1:1: warning: public symbol 'operation' is missing a doc string\n")
        record = self.build()
        self.assertTrue(record['docstrings'])
        self.commands.clear()
        with patch.object(sys, 'argv', ['check_docstrings.py']):
            self.assertEqual(check_docstrings.main(), 1)
        self.assertFalse(any(cmd[:2] == ['mojo', 'precompile'] for cmd in self.commands))

    def test_build_cannot_replace_packages_while_tests_hold_them(self):
        self.build()
        with build_state.prepared_build():
            with (self.output / '.library.lock').open('a') as lock:
                with self.assertRaises(BlockingIOError):
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with (self.output / '.library.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def test_source_change_during_test_invalidates_result(self):
        self.build()
        with self.assertRaisesRegex(SystemExit, 'sources or build inputs changed'):
            with build_state.prepared_build():
                (self.root / 'src/poly/new.mojo').write_text('# added during tests\n')

    def test_kernel_dependencies_must_match_library_identity(self):
        record = self.build()
        declared = patch.object(build_state, 'test_dependencies', return_value={'kernel': TEST_ONLY})
        declared.start()
        self.addCleanup(declared.stop)
        with self.assertRaisesRegex(SystemExit, '--tests-only'):
            with build_state.prepared_build(kernel=True):
                pass
        kernel = self.output / 'kernel'
        kernel.mkdir()
        stamp = kernel / 'library-build-id'
        stamp.write_text(record['build_id'] + '\n')
        with self.assertRaisesRegex(SystemExit, 'Missing kernel packages'):
            with build_state.prepared_build(kernel=True):
                pass
        for name in ('kernel_terms.mojoc', 'kernel_checks.mojoc'):
            (kernel / name).write_bytes(b'kernel')
        stamp.write_text('different-build\n')
        with self.assertRaisesRegex(SystemExit, '--tests-only'):
            with build_state.prepared_build(kernel=True):
                pass
        stamp.write_text(record['build_id'] + '\n')
        with build_state.prepared_build(kernel=True):
            pass

    def test_kernel_preparation_does_not_rebuild_library_or_public_dependency(self):
        record = self.build()
        self.commands.clear()
        with with_test_dependency(), \
                patch.object(build_state, 'test_dependencies', return_value={'kernel': TEST_ONLY}), \
                patch.object(deps, 'ROOT', self.root), \
                patch.object(deps, 'checkout', return_value=self.root / 'kernel-source') as checkout, \
                patch.object(deps, 'pins_of', return_value={}), \
                patch.object(sys, 'argv', ['deps.py', '--output', str(self.output), '--tests-only']):
            self.assertEqual(deps.main(), 0)
            self.assertEqual([call.args[0] for call in checkout.call_args_list], ['kernel'])
            compiles = [cmd for cmd in self.commands if cmd[:2] == ['mojo', 'precompile']]
            self.assertEqual([Path(cmd[-1]).name for cmd in compiles], ['kernel_terms.mojoc', 'kernel_checks.mojoc'])
            with build_state.prepared_build(kernel=True) as snapshot:
                self.assertEqual(snapshot.identity, record['build_id'])

    def test_fast_results_are_saved_before_slow_tests_finish(self):
        self.build()
        release = threading.Event()
        # Keep the slow test first even after the runner sorts paths into batches.
        fixtures = [(name, self.root / 'tests' / f'{index}_{name}', None, ())
                    for index, name in enumerate(('slow', 'fast'))]
        original_report = suite._report
        observed = []

        def execute(job, *_):
            if job[0] == 'slow':
                if not release.wait(5):
                    raise AssertionError('runner hid the fast result until the slow test finished')
            return dict(name=job[0], passed=True, detail='', seconds=0)

        def report(*args, **kwargs):
            original_report(*args, **kwargs)
            current = json.loads(args[0].read_text())
            if len(current['records']) == 1:
                observed.append(current)
                release.set()

        with patch.object(suite, 'jobs', return_value=fixtures), \
                patch.object(suite, 'prepare', return_value=fake_executable()), \
                patch.object(suite, 'source_inputs', return_value={}), \
                patch.object(suite, '_run', side_effect=execute), \
                patch.object(suite, '_report', side_effect=report), \
                patch.object(sys, 'argv', ['suite.py', '--batches', '1', '--jobs', '2', '--report', str(self.root / 'progress.json')]):
            self.assertEqual(suite.main(), 0)
        self.assertEqual(observed[0]['records'][0]['name'], 'fast')
        self.assertFalse(observed[0]['complete'])
        self.assertIsNone(observed[0]['passed'])


class CompilerDiagnosticTests(unittest.TestCase):
    def test_generated_members_are_excluded_but_authored_members_are_kept(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            source = root / 'example.mojo'
            source.write_text('struct Example:\n    def __init__(out self):\n')
            diagnostics = (
                "example.mojo:1:1: warning: public symbol '__init__' is missing a doc string\n"
                "example.mojo:2:5: warning: public symbol '__init__' is missing a doc string\n"
                "example.mojo:2:5: warning: deprecated operation\n")
            docs, warnings = compiler_diagnostics.classify(diagnostics, root)
            self.assertEqual(len(docs), 1)
            self.assertIn('example.mojo:2:', docs[0])
            self.assertEqual(warnings, ['example.mojo:2:5: warning: deprecated operation'])


if __name__ == '__main__':
    unittest.main()
