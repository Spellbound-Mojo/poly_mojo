"""Check the public array API against the shared library build.

Run with the repository's pinned Pixi environment. Reports live under --output;
cached executables cover the selected cases at O0 and O3. Compiler-rejection
checks run separately through check_rejections.py.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path

from build_state import prepared_build
from test_executable import prepare, CompilationFailed

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
EXPECTED = {
    "test_modular_gcd_archive.mojo": "modular gcd archive checks passed\n",
    "test_chunked_dense.mojo": "chunked dense checks passed\n",
    "test_dense_ingestion.mojo": "dense ingestion checks passed\n",
    "test_boundary_performance.mojo": "array boundary performance checks passed\n",
    "test_cleanup_adapters.mojo": "cleanup adapter checks passed\n",
    "test_fixed_cad_witness.mojo": "fixed CAD witness checks passed\n",
    "test_fixed_cad_edges.mojo": "fixed CAD edge checks passed\n",
    "test_fixed_cad_archive.mojo": "fixed CAD archive checks passed\n",
    "test_fixed_cad_geometry.mojo": "fixed CAD geometry checks passed\n",
    "test_fixed_cad_evidence.mojo": "fixed CAD evidence checks passed\n",
    "test_fixed_cad_stream.mojo": "fixed CAD stream checks passed\n",
    "test_fixed_cad_limits.mojo": "fixed CAD budget checks passed\n",
    "test_surface_scalars.mojo": "surface scalar arithmetic checks passed\n",
    "test_surface_interop.mojo": "surface representation interoperability checks passed\n",
    "test_surface_format.mojo": "surface named formatting checks passed\n",
    "test_surface_kernel.mojo": "surface kernel adapter checks passed\n",
    "test_access_numeric_interop.mojo": "access numerical interoperability checks passed\n",
    "test_access_astype.mojo": "access explicit dtype checks passed\n",
    "test_access_inspection.mojo": "access sparse inspection checks passed\n",
    "test_access_sturm.mojo": "access reusable Sturm checks passed\n",

    "test_workflow_specialization.mojo": "workflow specialization checks passed\n",
    "test_workflow_adaptive_fraction.mojo": "workflow adaptive fraction checks passed\n",
    "test_workflow_algebraic_covers.mojo": "workflow algebraic cover checks passed\n",
    "test_workflow_exact_stream.mojo": "workflow exact stream checks passed\n",
    "test_batch_axes.mojo": "batch axis checks passed\n",
    "test_batch_axes_polynomials.mojo": "polynomial batch axis checks passed\n",
    "test_completion_numeric_limits.mojo": "completion numerical limit checks passed\n",
    "test_completion_archive_diagnostics.mojo": "completion diagnostics archive checks passed\n",
    "test_completion_fraction_domains.mojo": "completion fraction domain checks passed\n",
    "test_completion_boundaries.mojo": "completion boundary checks passed\n",
    'test_completion_archive_algebraic.mojo': 'completion algebraic archive checks passed\n',
    'test_completion_archive_cad.mojo': 'completion cad archive checks passed\n',
    'test_completion_archive_cad_special.mojo': 'completion cad_special archive checks passed\n',
    'test_completion_archive_exact.mojo': 'completion exact archive checks passed\n',
    'test_completion_archive_rational.mojo': 'completion rational archive checks passed\n',
    'test_completion_archive_roots.mojo': 'completion roots archive checks passed\n',
    'test_completion_archive_stream.mojo': 'completion archive stream checks passed\n',
    'test_completion_rational_finite.mojo': 'completion finite rational checks passed\n',
    'test_completion_rational_numeric.mojo': 'completion numerical rational checks passed\n',
    'test_completion_resultants.mojo': 'completion determinant checks passed\n',
    'test_completion_root_numeric.mojo': 'completion algebraic numerical root checks passed\n',
    'test_completion_roots.mojo': 'completion algebraic root checks passed\n',

    "test_value_io_exact.mojo": "value serialization exact checks passed\n",
    "test_value_io_numeric.mojo": "value serialization numerical checks passed\n",
    "test_value_io_batch.mojo": "value serialization batch checks passed\n",
    "test_value_io_reject.mojo": "value serialization rejection checks passed\n",
    "test_value_io_stream.mojo": "value serialization stream checks passed\n",
    "test_value_io_limits.mojo": "value serialization budget checks passed\n",

    "test_refinement_receipt.mojo": "array algebraic refinement receipt checks passed\n",
    "test_refinement_stream.mojo": "array algebraic refinement stream checks passed\n",
    "test_refinement_reject.mojo": "array algebraic refinement rejection checks passed\n",
    "test_refinement_limits.mojo": "array algebraic refinement budget checks passed\n",
    "test_numeric_algebraic_limits.mojo": "array algebraic numerical limit checks passed\n",
    "test_numeric_algebraic.mojo": "array algebraic numerical conversion checks passed\n",
    "test_numeric_algebraic_evaluation.mojo": "array algebraic numerical evaluation checks passed\n",
    "test_serial_algebraic.mojo": "array algebraic serialization checks passed\n",
    "test_serial_algebraic_reject.mojo": "array algebraic serialization rejection checks passed\n",
    "test_serial_algebraic_stream.mojo": "array algebraic serialization stream checks passed\n",
    "test_factor_algebraic_multivariate_orders.mojo": "array multivariate algebraic order checks passed\n",
    "test_factor_algebraic_multivariate.mojo": "array multivariate real algebraic factor checks passed\n",
    "test_factor_algebraic_multivariate_complex.mojo": "array multivariate complex algebraic factor checks passed\n",
    "test_factor_algebraic_multivariate_evidence.mojo": "array multivariate algebraic evidence checks passed\n",
    "test_factor_algebraic_multivariate_limits.mojo": "array multivariate algebraic budget checks passed\n",
    "test_factor_algebraic.mojo": "array algebraic factorization checks passed\n",
    "test_factor_algebraic_sparse.mojo": "array sparse algebraic factorization checks passed\n",
    "test_factor_algebraic_pairs.mojo": "array algebraic conjugate factor checks passed\n",
    "test_factor_algebraic_evidence.mojo": "array algebraic factor evidence checks passed\n",
    "test_factor_algebraic_limits.mojo": "array algebraic factor budget checks passed\n",
    'test_complex_roots_filtering.mojo': 'array complex root filtering checks passed\n',
    'test_complex_roots.mojo': 'array exact complex root checks passed\n',
    'test_complex_roots_projection.mojo': 'array complex root projection checks passed\n',
    'test_complex_roots_algebraic.mojo': 'array algebraic complex root checks passed\n',
    'test_complex_roots_boundaries.mojo': 'array complex root boundary checks passed\n',

    'test_algebraic_boundaries.mojo': 'array algebraic boundary checks passed\n',
    'test_algebraic_complex.mojo': 'array complex algebraic operation checks passed\n',
    'test_algebraic_operations.mojo': 'array algebraic operation checks passed\n',
    'test_algebraic_domains.mojo': 'array algebraic domain checks passed\n',
    'test_parity_domains.mojo': 'array parity domain checks passed\n',
    'test_parity_exact.mojo': 'array parity exact checks passed\n',
    'test_parity_cad.mojo': 'array parity CAD checks passed\n',
    'test_parity_streams.mojo': 'array parity stream checks passed\n',
    'test_parity_boundaries.mojo': 'array parity boundary checks passed\n',

    'test_extension_boundaries.mojo': 'array extension boundaries checks passed\n',
    'test_extension_numeric_operations.mojo': 'array extension numeric_operations checks passed\n',
    'test_extension_numeric_representations.mojo': 'array extension numeric_representations checks passed\n',
    'test_extension_algebraic_roots.mojo': 'array extension algebraic_roots checks passed\n',
    'test_extension_certified_evaluation.mojo': 'array extension certified_evaluation checks passed\n',

    'test_gap_boundaries.mojo': 'array gap boundaries checks passed\n',
    'test_gap_numeric.mojo': 'array gap numeric checks passed\n',
    'test_gap_batch.mojo': 'array gap batch checks passed\n',
    'test_gap_algebraic.mojo': 'array gap algebraic checks passed\n',
    'test_gap_roots.mojo': 'array gap roots checks passed\n',
    'test_gap_serialization.mojo': 'array gap serialization checks passed\n',

    'test_toolkit_fields.mojo': 'array toolkit field checks passed\n',
    'test_toolkit_boundaries.mojo': 'array toolkit boundary checks passed\n',
    'test_toolkit_series.mojo': 'array toolkit series checks passed\n',
    'test_toolkit_basis.mojo': 'array toolkit basis checks passed\n',
    'test_rational_algebraic_limits.mojo': 'array algebraic rational limit checks passed\n',
    'test_rational_algebraic.mojo': 'array algebraic rational checks passed\n',
    'test_rational_algebraic_local.mojo': 'array algebraic rational local checks passed\n',
    'test_rational_certificate_fields.mojo': 'array rational certificate field checks passed\n',
    'test_rational_certificates.mojo': 'array rational certificate checks passed\n',
    'test_rational_certificate_reject.mojo': 'array rational certificate rejection checks passed\n',
    'test_rational_certificate_limits.mojo': 'array rational certificate budget checks passed\n',
    'test_toolkit_rational.mojo': 'array toolkit rational checks passed\n',

    'test_solver_boundaries.mojo': 'array solver boundary checks passed\n',
    'test_root_values.mojo': 'array root value checks passed\n',
    'test_root_covers.mojo': 'array root cover checks passed\n',
    'test_ideals.mojo': 'array ideal checks passed\n',
    'test_cad_fiber_limits.mojo': 'array CAD fiber budget checks passed\n',
    'test_cad_fiber_geometry.mojo': 'array CAD fiber geometry checks passed\n',
    'test_cad_fiber_evidence.mojo': 'array CAD fiber evidence checks passed\n',
    'test_cad_fiber_stream.mojo': 'array CAD fiber stream checks passed\n',
    'test_cad_algebraic.mojo': 'array algebraic CAD checks passed\n',
    'test_cad_algebraic_special.mojo': 'array algebraic CAD specialized checks passed\n',
    'test_cad_algebraic_stream.mojo': 'array algebraic CAD stream checks passed\n',
    'test_cad_api.mojo': 'array CAD checks passed\n',
    'test_solver_streams.mojo': 'array solver stream checks passed\n',

    'test_interop.mojo': 'array interoperability checks passed\n',
    'test_exact_algebra.mojo': 'array exact algebra checks passed\n',
    'test_interpolation.mojo': 'array interpolation checks passed\n',
    'test_factor_domains.mojo': 'array factor domain checks passed\n',
    'test_factor_sparse.mojo': 'array sparse factor checks passed\n',
    'test_factorization.mojo': 'array factorization checks passed\n',
    'test_substitution.mojo': 'array substitution checks passed\n',
    'test_exact_edges.mojo': 'array exact boundary checks passed\n',
    'test_boundary.mojo': 'array boundary checks passed\n',
    'test_operations.mojo': 'array operation checks passed\n',
    'test_evaluation.mojo': 'array evaluation checks passed\n',
    'example.mojo': json.loads((ROOT / 'docs/examples.json').read_text())['examples']['docs/examples/array_api.mojo']['stdout'],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / '.cache/array-api')
    parser.add_argument('--build', default='build', help='Prepared library directory')
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--timeout', type=int, default=300, help='Runtime timeout per test in seconds')
    parser.add_argument('--compiler-threads', type=int, default=2, help='Threads in the single compiler process (default: 2)')
    parser.add_argument('--compile-timeout', type=float, help='Optional timeout per suite compilation')
    parser.add_argument('--only', help='Check case names containing this substring')
    args = parser.parse_args()
    with prepared_build(args.build) as snapshot:
        records, executables = check(args, snapshot, parser)
    passed = all(record['passed'] for record in records)
    (args.output.resolve() / 'report.json').write_text(json.dumps(
        dict(passed=passed, library_build=snapshot.report(), executables=executables, records=records), indent=2) + '\n')
    print('ARRAY API CHECKS PASS' if passed else 'ARRAY API CHECKS FAILED', flush=True)
    return not passed


def check(args, snapshot, parser):
    folder = args.output.resolve()
    folder.mkdir(parents=True, exist_ok=True)
    selected = {name: (ROOT / 'docs/examples/array_api.mojo' if name == 'example.mojo'
                       else ROOT / 'tests/poly' / name)
                for name in EXPECTED if not args.only or args.only in name}
    if not selected:
        parser.error('No runtime cases match --only; use check_rejections.py for rejection checks')
    print(f'Using library build {snapshot.identity}: {snapshot.path}', flush=True)
    records, executables = [], []
    for level in (0, 3):
        try:
            executable = prepare(list(selected.values()), snapshot, ROOT,
                                 flags=('--Werror', f'-O{level}'), timeout=args.compile_timeout, compiler_threads=args.compiler_threads)
        except CompilationFailed as error:
            records.append(dict(name=f'suite-O{level}', passed=False, compile=error.record['compile'], run=None))
            break
        executables.append(executable.report())

        def positive(item):
            name, path = item
            executed = executable.execute(path, ROOT, args.timeout)
            passed = executed['returncode'] == 0 and executed['stdout'] == EXPECTED[name]
            label = f'{Path(name).stem}-package-O{level}'
            print(('PASS ' if passed else 'FAIL ') + label, flush=True)
            return dict(name=label, passed=passed, compile=executable.record['compile'], run=executed)

        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as executor:
            records.extend(executor.map(positive, selected.items()))
    return records, executables


if __name__ == '__main__':
    raise SystemExit(main())
