"""Driver reuse and unavailable external-memory measurements keep honest records."""
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

from harness import cad, report, run, tools


class SharedBuild(unittest.TestCase):
    def test_modes_share_one_driver_and_reuse_it(self):
        with tempfile.TemporaryDirectory() as directory:
            binary = Path(directory) / 'driver'
            calls = []

            class Driver:
                def builds(self, cases):
                    return [(2, False)]

                def binary(self, *key):
                    return binary

                def build(self, *key):
                    calls.append(key)
                    binary.write_bytes(b'executable')
                    return binary, 1.0, 1

            selected = [Driver(), Driver()]
            self.assertEqual(len(tools.prebuild(selected, [], 2)), 1)
            self.assertEqual(tools.prebuild(selected, [], 2), [])
            self.assertEqual(calls, [(2, False)])

    def test_shared_library_is_validated_once_without_rebuilding(self):
        selected = [SimpleNamespace(system='Poly Mojo'), SimpleNamespace(system='Poly Mojo')]
        with patch.object(tools, 'verify_library', return_value='build-id') as validate:
            self.assertEqual(tools.verify_poly_mojo(selected), {str((tools.ROOT / 'build').resolve()): 'build-id'})
            validate.assert_called_once()


class MissingMemory(unittest.TestCase):
    def baseline(self, allow):
        with tempfile.TemporaryDirectory() as directory:
            tool = SimpleNamespace(in_process=False, name='external',
                                   baseline_input=lambda case, work: (['external'], {}))
            settings = {'scratch': Path(directory), 'memory': 1024, 'cpu': 0,
                        'allow_missing_memory': allow}
            process = SimpleNamespace(wall_s=0.01, cgroup_peak_kb=None)
            with patch.object(run.measure, 'run', return_value=process):
                return run.baseline_for(tool, {'variables': ['x'], 'field': None}, settings, {})

    def test_missing_memory_requires_explicit_opt_in(self):
        with self.assertRaises(SystemExit):
            self.baseline(False)
        self.assertEqual(self.baseline(True), {'wall_s': 0.01, 'cgroup_peak_kb': None})

    def test_missing_memory_is_not_a_zero_or_a_comparison(self):
        base = dict(case='example', tool='polymojo', field=None, order='lex',
                    outcome='ok', agreement='confirmed', peak_incremental_kib=2048)
        peer = dict(base, tool='msolve', peak_incremental_kib=None)
        groups, _, _ = report.ratios([base, peer], ['polymojo', 'msolve'], 'peak_incremental_kib', 1024)
        self.assertFalse(groups)
        self.assertEqual(report.fmt_mem(None), 'n/a')

    def test_report_states_when_requested_cap_was_not_enforced(self):
        rows = [{'memory_cap': '12G', 'process': {'memory_capped': False}}]
        self.assertIn('not enforced', report.memory_limit(rows))
        rows[0]['process']['memory_capped'] = True
        self.assertEqual(report.memory_limit(rows), 'Memory cap: 12G.')


class QepcadVersion(unittest.TestCase):
    def test_version_comes_from_the_selected_build(self):
        with tempfile.TemporaryDirectory() as directory:
            banner = Path(directory) / 'source/main/PRINTBANNER.c'
            banner.parent.mkdir(parents=True)
            banner.write_text('static const char* version = "1.80";\n')
            with patch.dict('os.environ', {'QEPCAD_HOME': directory, 'TARSKI_COMMIT': 'pin'}):
                self.assertEqual(cad.Qepcad('fullcad').version(), 'QEPCAD B 1.80 (Tarski pin)')


if __name__ == '__main__':
    unittest.main()
