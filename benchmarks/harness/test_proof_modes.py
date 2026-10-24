"""Peer ratios and certificate tables must identify the work being timed."""
import unittest
from pathlib import Path
import tempfile
from contextlib import redirect_stdout
import io
import json
from types import SimpleNamespace
from unittest.mock import patch

from harness import cad, gcd, proofs, real_roots, report, tools


class ProofModes(unittest.TestCase):
    def test_peer_ratio_uses_fully_uncertified_groebner(self):
        base = dict(case='one', field=None, order='lex', outcome='ok', agreement='confirmed')
        records = [base | dict(tool='polymojo', time_s=2),
                   base | dict(tool='polymojo-uncertified', time_s=1),
                   base | dict(tool='sympy-buchberger', time_s=3)]
        groups, _, _ = report.ratios(records, [], 'time_s', 0.01)
        self.assertEqual(groups['QQ', 'lex']['sympy-buchberger'], [3])

    def test_distinguishes_internal_certification_from_no_certificate(self):
        case = {'family': 'groebner'}
        self.assertEqual(proofs.metadata(tools.PolyMojo(mode='uncertified'), case)['proof_mode'], 'none')
        self.assertEqual(proofs.metadata(tools.PolyMojo(), case)['proof_mode'], 'internal-certification')
        self.assertEqual(proofs.metadata(tools.PolyMojo(certified=True), case)['proof_mode'], 'retained')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'build').mkdir()
            (root / 'build/library-build.json').write_text('{}')
            with patch.object(gcd, 'ROOT', root):
                self.assertEqual(gcd.PolyMojoGcd(certified=True).binary(2, False), gcd.PolyMojoGcd().binary(2, False))

    def test_certificate_table_keeps_check_separate(self):
        records = [dict(case='one', tool='plain', outcome='ok', time_s=1),
                   dict(case='one', tool='checked', outcome='ok', time_s=2, check_s=3)]
        row = proofs.table(records, [('plain', 'checked')])[-1]
        self.assertIn('| 1 s | 2 s | 3 s | 5 s |', row)

    def test_root_certificate_rejection_is_not_overwritten(self):
        tool = real_roots.PolyMojoRoots()
        with patch.object(real_roots, 'check', return_value=True):
            result = tool.finish({}, {'check_ok': False}, 2, None)
        self.assertFalse(result['check_ok'])
        self.assertEqual(proofs.metadata(tool, {'family': 'roots'})['proof_mode'], 'always-retained')

    def test_cad_peer_ratio_excludes_final_verification(self):
        base = dict(case='full-example', outcome='ok', cells=1, projection_factors=[1, 1])
        rows = [base | dict(tool='polymojo-construct', time_s=1, check_s=2),
                base | dict(tool='polymojo-final', time_s=3, check_s=2),
                base | dict(tool='qepcad-fullcad', time_s=0.5)]
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            (folder / 'records.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in rows))
            with redirect_stdout(io.StringIO()):
                cad.main_report(SimpleNamespace(folder=folder))
            rendered = (folder / 'report.md').read_text()
        self.assertIn(' | 2.00 | ', rendered)
        self.assertIn('| full-example | 1 | 2 | 3 | 3 |', rendered)
        self.assertIn('not a proof-free public API', rendered)


if __name__ == '__main__':
    unittest.main()
