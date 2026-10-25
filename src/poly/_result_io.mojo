"""Typed certificate archives; field order is the version-one wire schema.

Only the result families implementing _Archive can enter this codec. Containers
are decoded incrementally, polynomial invariants are checked before use, and the
root result's independent checker must accept the complete restored evidence.
"""
from . import sparse
from std.builtin.rebind import downcast
from std.reflection import reflect
from std.memory import ArcPointer
import polynomials as core
import apn_mojo as apn
from polynomials import Budget, PolyError, PolyErrorKind, CoefficientRing, CoefficientField, NumericDomain, PolynomialTextSource, PolynomialTextSink
from . import _common, _value_io, _algebraic_value
from ._common import _CoreKind, _allocation, _grow, _charge_size
from ._archive_meta import _Archive
from ._io_meta import _Record
from ._algebraic_io import _Reader, _Writer, _bad
from . import exact, roots, cad, _cad_algebraic, _cad_fixed, _complex_roots, _algebraic_numeric, _rational_field, _rational_certificates, _determinant, algebraic


def _tag[T: Copyable & Deinitable](mut budget: Budget) raises PolyError -> String:
    comptime V = downcast[T, _Archive]
    var name = String("CHECKED-1:", reflect[T].name(), ":axes=", V._archive_shape())
    if name.find("cad.Solution[") >= 0:
        # Revision 10: conjunction solutions carry coverings evidence.
        name = String("CHECKED-2:", reflect[T].name(), ":axes=", V._archive_shape())
    if name.find("roots.RootCount:") >= 0:
        # Revision 11: root counts carry Descartes evidence; Sturm-era archives are rejected.
        name = String("CHECKED-2:", reflect[T].name(), ":axes=", V._archive_shape())
    if name.find("cad.Decomposition[") >= 0 or name.find("cad.Covering[") >= 0:
        # Revision 16: final-data CAD evidence; legacy CHECKED-1 remains readable.
        name = String("CHECKED-3:", reflect[T].name(), ":axes=", V._archive_shape())
    _charge_size(name.byte_length(), budget)
    return name^


def _legacy_cad_tag[T: _Archive](tag: String, mut budget: Budget) raises PolyError -> Bool:
    var name = String(reflect[T].name())
    if name.find("cad.Decomposition[") < 0 and name.find("cad.Covering[") < 0:
        return False
    var expected = String("CHECKED-1:", name, ":axes=", T._archive_shape())
    _charge_size(expected.byte_length(), budget)
    return tag == expected


def _write[T: _Archive, S: PolynomialTextSink](value: T, mut writer: _Writer, mut sink: S, mut budget: Budget) raises PolyError:
    if not value._archive_check(budget):
        raise _bad("result does not carry accepted evidence")
    value._archive_write(writer, sink, budget, 0)


def _read[T: _Archive, S: PolynomialTextSource](mut reader: _Reader[S], mut budget: Budget) raises PolyError -> T:
    var value = T._archive_read(reader, budget, 0)
    if not value._archive_check(budget):
        raise _bad("restored result failed independent verification")
    return value^


def _depth(depth: Int, mut budget: Budget) raises PolyError:
    budget.charge(1)
    if depth > 256:
        raise _bad("certificate nesting exceeds 256 levels")


@fieldwise_init
struct _PendingFinalCAD(Movable):
    var kind: Int
    var variables: List[Int64]
    var bytes: List[UInt8]
    var legacy: Optional[core.CADCertificate]
    var covering: Optional[core.CADCoveringCertificate]


def _write_final_cad[C: CoefficientRing, D: NumericDomain, E: Copyable & Deinitable, S: PolynomialTextSink](proof: core.CADFinalCertificate, mut writer: _Writer, mut sink: S, mut budget: Budget, depth: Int) raises PolyError:
    if proof.is_compact():
        writer.line("0", sink, budget)
        var variables = proof.variables(budget)
        writer.line(String(len(variables)), sink, budget)
        for axis in variables:
            writer.line(String(axis), sink, budget)
        var bytes = proof.compact_bytes(budget)
        writer.line(String(len(bytes)), sink, budget)
        var hex = String("0123456789abcdef")
        for start in range(0, len(bytes), 2048):
            var text = String()
            for k in range(start, min(start + 2048, len(bytes))):
                _charge_size(2, budget)
                var high = Int(bytes[k] >> 4)
                var low = Int(bytes[k] & 15)
                text.write(hex[byte=high:high + 1], hex[byte=low:low + 1])
            writer.line(text, sink, budget)
    elif proof.legacy_decomposition():
        writer.line("1", sink, budget)
        _write_node[core.CADCertificate, C, D, E](proof.legacy_decomposition().value(), writer, sink, budget, depth + 1)
    elif proof.legacy_covering():
        writer.line("2", sink, budget)
        _write_node[core.CADCoveringCertificate, C, D, E](proof.legacy_covering().value(), writer, sink, budget, depth + 1)
    else:
        raise _bad("missing final CAD payload")


def _hex_final(byte: UInt8) raises PolyError -> UInt8:
    if byte >= 48 and byte <= 57:
        return byte - 48
    if byte >= 97 and byte <= 102:
        return byte - 87
    raise _bad("noncanonical compact CAD hexadecimal digit")


def _read_final_cad[C: CoefficientRing, D: NumericDomain, E: Copyable & Deinitable, S: PolynomialTextSource](mut reader: _Reader[S], query: Bool, mut budget: Budget, depth: Int) raises PolyError -> _PendingFinalCAD:
    var kind = (2 if query else 1) if reader.legacy_cad_archive else Int(reader.number(2, budget))
    var pending = _PendingFinalCAD(kind, List[Int64](), List[UInt8](), None, None)
    if kind == 0:
        var count = reader.count(budget)
        for _ in range(count):
            var axis = reader.identifier(budget)
            _grow(pending.variables, budget)
            pending.variables.append(axis)
        var length = reader.count(budget)
        while len(pending.bytes) < length:
            var text = reader.line(budget)
            var count = min(2048, length - len(pending.bytes))
            if text.byte_length() != 2 * count:
                raise _bad("incorrect compact CAD hexadecimal chunk length")
            var digits = text.as_bytes()
            for k in range(count):
                var byte = (_hex_final(digits[2 * k]) << 4) | _hex_final(digits[2 * k + 1])
                _grow(pending.bytes, budget)
                pending.bytes.append(byte)
    elif kind == 1 and not query:
        pending.legacy = _read_node[core.CADCertificate, C, D, E](reader, budget, depth + 1)
    elif kind == 2 and query:
        pending.covering = _read_node[core.CADCoveringCertificate, C, D, E](reader, budget, depth + 1)
    else:
        raise _bad("CAD payload does not match the requested claim")
    return pending^


def _accept_final_cad(var pending: _PendingFinalCAD, inputs: List[core.SparsePoly[core.QQ]], masks: List[UInt8], query: Bool, embedding: Optional[ArcPointer[_cad_algebraic._Embedding]], fixed: List[Tuple[Int, algebraic.Real]], mut budget: Budget) raises PolyError -> core.CADFinalCertificate:
    var prefix = _cad_fixed._prefix(embedding, fixed, budget)
    if pending.kind == 0:
        if len(prefix):
            raise _bad("compact full-space CAD cannot claim a fixed prefix")
        return core.CADFinalCertificate.from_compact_bytes(Span(pending.bytes), inputs, pending.variables, masks, query, budget)
    if pending.kind == 1:
        return core.CADFinalCertificate.from_legacy(pending.legacy.take(), inputs, prefix, budget)
    return core.CADFinalCertificate.from_legacy_covering(pending.covering.take(), inputs, masks, prefix, budget)


def _write_node[T: Copyable & Deinitable, C: CoefficientRing, D: NumericDomain, E: Copyable & Deinitable, S: PolynomialTextSink](value: T, mut writer: _Writer, mut sink: S, mut budget: Budget, depth: Int) raises PolyError:
    _depth(depth, budget)
    comptime F = downcast[C, CoefficientField] if conforms_to(C, CoefficientField) else core.QQ
    comptime if (T == core.NumericDensePoly[core.FloatDomain] or T == core.NumericSparsePoly[core.FloatDomain] or T == core.EnclosureEvaluation[core.FloatDomain] or T == core.AdaptiveEvaluation[core.FloatDomain]) and D != core.FloatDomain:
        _write_node[T, C, core.FloatDomain, E](value, writer, sink, budget, depth + 1)
    elif (T == core.NumericDensePoly[core.ComplexDomain] or T == core.NumericSparsePoly[core.ComplexDomain] or T == core.EnclosureEvaluation[core.ComplexDomain] or T == core.AdaptiveEvaluation[core.ComplexDomain]) and D != core.ComplexDomain:
        _write_node[T, C, core.ComplexDomain, E](value, writer, sink, budget, depth + 1)
    elif (T == core.NumericDensePoly[core.BallDomain] or T == core.NumericSparsePoly[core.BallDomain] or T == core.EnclosureEvaluation[core.BallDomain] or T == core.AdaptiveEvaluation[core.BallDomain]) and D != core.BallDomain:
        _write_node[T, C, core.BallDomain, E](value, writer, sink, budget, depth + 1)
    elif (T == core.NumericDensePoly[core.ComplexBallDomain] or T == core.NumericSparsePoly[core.ComplexBallDomain] or T == core.EnclosureEvaluation[core.ComplexBallDomain] or T == core.AdaptiveEvaluation[core.ComplexBallDomain]) and D != core.ComplexBallDomain:
        _write_node[T, C, core.ComplexBallDomain, E](value, writer, sink, budget, depth + 1)
    elif (T == core.DensePoly[core.QQ] or T == core.SparsePoly[core.QQ]) and C != core.QQ:
        _write_node[T, core.QQ, D, E](value, writer, sink, budget, depth + 1)
    elif (T == core.DensePoly[core.ZZ] or T == core.SparsePoly[core.ZZ]) and C != core.ZZ:
        _write_node[T, core.ZZ, D, E](value, writer, sink, budget, depth + 1)
    elif (T == core.DensePoly[core.QQi] or T == core.SparsePoly[core.QQi]) and C != core.QQi:
        _write_node[T, core.QQi, D, E](value, writer, sink, budget, depth + 1)
    elif (T == core.DensePoly[_algebraic_value.Real] or T == core.SparsePoly[_algebraic_value.Real]) and C != _algebraic_value.Real:
        _write_node[T, _algebraic_value.Real, D, E](value, writer, sink, budget, depth + 1)
    elif (T == core.DensePoly[_algebraic_value.Complex] or T == core.SparsePoly[_algebraic_value.Complex]) and C != _algebraic_value.Complex:
        _write_node[T, _algebraic_value.Complex, D, E](value, writer, sink, budget, depth + 1)
    elif (T == core.DensePoly[core.ModInt] or T == core.SparsePoly[core.ModInt]) and C != core.ModInt:
        _write_node[T, core.ModInt, D, E](value, writer, sink, budget, depth + 1)
    elif conforms_to(T, _Archive):
        rebind[downcast[T, _Archive]](value)._archive_write(writer, sink, budget, depth)
    elif conforms_to(T, _Record) or _value_io._Supported[T]:
        _value_io._write(value, writer, sink, budget)
    elif conforms_to(T, sparse._Powers):
        var monomial = sparse._monomial(value, budget)
        _write_node[core.Monomial, C, D, E](monomial, writer, sink, budget, depth + 1)
    elif T == Int:
        writer.line(String(rebind_var[Int](value.copy())), sink, budget)
    elif T == Int64:
        writer.line(String(rebind_var[Int64](value.copy())), sink, budget)
    elif T == UInt64:
        writer.line(String(rebind_var[UInt64](value.copy())), sink, budget)
    elif T == UInt32:
        writer.line(String(rebind_var[UInt32](value.copy())), sink, budget)
    elif T == UInt8:
        writer.line(String(rebind_var[UInt8](value.copy())), sink, budget)
    elif T == Bool:
        writer.line(String(Int(rebind_var[Bool](value.copy()))), sink, budget)
    elif T == core.NoContext:
        budget.charge(1)
    elif T == core.Modulus:
        writer.line(String(rebind[core.Modulus](value).value), sink, budget)
    elif T == core.QQ:
        writer.line(_value_io._qtext(rebind[core.QQ](value), budget), sink, budget)
    elif T == core.ZZ:
        _value_io._write(rebind[core.ZZ](value).value, writer, sink, budget)
    elif T == core.QQi:
        _value_io._write(rebind[core.QQi](value).value, writer, sink, budget)
    elif T == core.RealAlgebraic:
        writer.real(_algebraic_value._plain(_algebraic_value._copy_witness(rebind[core.RealAlgebraic](value), budget), budget), sink, budget)
    elif T == core.NumericOutcome:
        writer.line(String(rebind[core.NumericOutcome](value).code), sink, budget)
    elif T == core.Monomial:
        ref v = rebind[core.Monomial](value)
        writer.line(String(len(v.pairs)), sink, budget)
        for field6 in v.pairs:
            _write_node[Int64, C, D, E](field6[0], writer, sink, budget, depth + 1)
            _write_node[UInt32, C, D, E](field6[1], writer, sink, budget, depth + 1)
    elif T == core.MonomialOrder:
        ref v = rebind[core.MonomialOrder](value)
        _write_node[UInt8, C, D, E](v.kind, writer, sink, budget, depth + 1)
        writer.line(String(len(v.variables)), sink, budget)
        for field11 in v.variables:
            _write_node[Int64, C, D, E](field11, writer, sink, budget, depth + 1)
    elif T == core.DensePoly[C]:
        ref v = rebind[core.DensePoly[C]](value)
        _write_node[Int64, C, D, E](v.variable, writer, sink, budget, depth + 1)
        _write_node[C.Context, C, D, E](v.ring, writer, sink, budget, depth + 1)
        writer.line(String(len(v.coefficients)), sink, budget)
        for index in range(len(v.coefficients)):
            ref field17 = v.coefficients[index]
            _write_node[C, C, D, E](field17, writer, sink, budget, depth + 1)
    elif T == core.Term[C]:
        ref v = rebind[core.Term[C]](value)
        _write_node[core.Monomial, C, D, E](v.monomial, writer, sink, budget, depth + 1)
        _write_node[C, C, D, E](v.coefficient, writer, sink, budget, depth + 1)
    elif T == core.SparsePoly[C]:
        ref v = rebind[core.SparsePoly[C]](value)
        _write_node[core.MonomialOrder, C, D, E](v.order, writer, sink, budget, depth + 1)
        _write_node[C.Context, C, D, E](v.ring, writer, sink, budget, depth + 1)
        writer.line(String(len(v.terms)), sink, budget)
        for field25 in v.terms:
            _write_node[core.Term[C], C, D, E](field25, writer, sink, budget, depth + 1)
    elif T == core.NumericDensePoly[D]:
        ref v = rebind[core.NumericDensePoly[D]](value)
        _write_node[Int64, C, D, E](v.variable, writer, sink, budget, depth + 1)
        writer.line(String(len(v.coefficients)), sink, budget)
        for field30 in v.coefficients:
            _write_node[D.Scalar, C, D, E](field30, writer, sink, budget, depth + 1)
    elif T == core.NumericTerm[D]:
        ref v = rebind[core.NumericTerm[D]](value)
        _write_node[core.Monomial, C, D, E](v.monomial, writer, sink, budget, depth + 1)
        _write_node[D.Scalar, C, D, E](v.coefficient, writer, sink, budget, depth + 1)
    elif T == core.NumericSparsePoly[D]:
        ref v = rebind[core.NumericSparsePoly[D]](value)
        _write_node[core.MonomialOrder, C, D, E](v.order, writer, sink, budget, depth + 1)
        writer.line(String(len(v.terms)), sink, budget)
        for field37 in v.terms:
            _write_node[core.NumericTerm[D], C, D, E](field37, writer, sink, budget, depth + 1)
    elif T == core.NumericOptions:
        ref v = rebind[core.NumericOptions](value)
        _write_node[Int, C, D, E](v.initial_precision, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.max_precision, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.absolute_bits, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.relative_bits, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.max_subdivisions, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.require_isolation, writer, sink, budget, depth + 1)
    elif T == core.MembershipCertificate[C]:
        ref v = rebind[core.MembershipCertificate[C]](value)
        writer.line(String(len(v.cofactors)), sink, budget)
        for field47 in v.cofactors:
            _write_node[core.SparsePoly[C], C, D, E](field47, writer, sink, budget, depth + 1)
    elif T == core.SquarefreeDecomposition[C]:
        ref v = rebind[core.SquarefreeDecomposition[C]](value)
        _write_node[C, C, D, E](v.unit, writer, sink, budget, depth + 1)
        writer.line(String(len(v.factors)), sink, budget)
        for field54 in v.factors:
            _write_node[core.DensePoly[C], C, D, E](field54[0], writer, sink, budget, depth + 1)
            _write_node[Int, C, D, E](field54[1], writer, sink, budget, depth + 1)
    elif T == core.Factorization[C]:
        ref v = rebind[core.Factorization[C]](value)
        _write_node[C, C, D, E](v.unit, writer, sink, budget, depth + 1)
        writer.line(String(len(v.factors)), sink, budget)
        for field61 in v.factors:
            _write_node[core.DensePoly[C], C, D, E](field61[0], writer, sink, budget, depth + 1)
            _write_node[Int, C, D, E](field61[1], writer, sink, budget, depth + 1)
    elif T == core.DivisionResult[C]:
        ref v = rebind[core.DivisionResult[C]](value)
        _write_node[core.DensePoly[C], C, D, E](v.quotient, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[C], C, D, E](v.remainder, writer, sink, budget, depth + 1)
    elif T == core.ListDivision[C]:
        ref v = rebind[core.ListDivision[C]](value)
        writer.line(String(len(v.quotients)), sink, budget)
        for field68 in v.quotients:
            _write_node[core.SparsePoly[C], C, D, E](field68, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.remainder, writer, sink, budget, depth + 1)
    elif T == core.ContentGcdStep[C]:
        ref v = rebind[core.ContentGcdStep[C]](value)
        _write_node[core.SparsePoly[C], C, D, E](v.gcd, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.cofactors[0], writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.cofactors[1], writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.coprimality_node))), sink, budget)
        if v.coprimality_node:
            _write_node[Int, C, D, E](v.coprimality_node.value(), writer, sink, budget, depth + 1)
    elif T == core.CoprimalityNode[C]:
        ref v = rebind[core.CoprimalityNode[C]](value)
        _write_node[Int64, C, D, E](v.variable, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.u, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.v, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.s, writer, sink, budget, depth + 1)
        writer.line(String(len(v.left_content_steps)), sink, budget)
        for field87 in v.left_content_steps:
            _write_node[core.ContentGcdStep[C], C, D, E](field87, writer, sink, budget, depth + 1)
        writer.line(String(len(v.right_content_steps)), sink, budget)
        for field88 in v.right_content_steps:
            _write_node[core.ContentGcdStep[C], C, D, E](field88, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.contents_node))), sink, budget)
        if v.contents_node:
            _write_node[Int, C, D, E](v.contents_node.value(), writer, sink, budget, depth + 1)
    elif T == core.CoprimalityCertificate[C]:
        ref v = rebind[core.CoprimalityCertificate[C]](value)
        writer.line(String(len(v.nodes)), sink, budget)
        for field93 in v.nodes:
            _write_node[core.CoprimalityNode[C], C, D, E](field93, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.root, writer, sink, budget, depth + 1)
    elif T == core.GcdResult[C]:
        ref v = rebind[core.GcdResult[C]](value)
        _write_node[core.SparsePoly[C], C, D, E](v.gcd, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.cofactors[0], writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.cofactors[1], writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.bezout))), sink, budget)
        if v.bezout:
            _write_node[core.SparsePoly[C], C, D, E](v.bezout.value()[0], writer, sink, budget, depth + 1)
            _write_node[core.SparsePoly[C], C, D, E](v.bezout.value()[1], writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.coprimality))), sink, budget)
        if v.coprimality:
            _write_node[core.CoprimalityCertificate[C], C, D, E](v.coprimality.value(), writer, sink, budget, depth + 1)
    elif T == core.ResultantResult[C]:
        ref v = rebind[core.ResultantResult[C]](value)
        _write_node[core.SparsePoly[C], C, D, E](v.resultant, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.cofactors[0], writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.cofactors[1], writer, sink, budget, depth + 1)
    elif T == core.SturmSequence:
        ref v = rebind[core.SturmSequence](value)
        writer.line(String(len(v.polynomials)), sink, budget)
        for field114 in v.polynomials:
            _write_node[core.DensePoly[core.QQ], C, D, E](field114, writer, sink, budget, depth + 1)
        writer.line(String(len(v.quotients)), sink, budget)
        for field115 in v.quotients:
            _write_node[core.DensePoly[core.QQ], C, D, E](field115, writer, sink, budget, depth + 1)
    elif T == core.DescartesCountCertificate:
        ref v = rebind[core.DescartesCountCertificate](value)
        _write_node[core.AlgebraicDescartesCertificate, C, D, E](v.isolation, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.a, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.b, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.count, writer, sink, budget, depth + 1)
    elif T == core.RootCountCertificate:
        ref v = rebind[core.RootCountCertificate](value)
        _write_node[core.SturmSequence, C, D, E](v.sequence, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.a, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.b, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.count, writer, sink, budget, depth + 1)
    elif T == core.CancellationCertificate:
        ref v = rebind[core.CancellationCertificate](value)
        _write_node[core.SparsePoly[core.QQ], C, D, E](v.common, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[core.QQ], C, D, E](v.cofactors[0], writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[core.QQ], C, D, E](v.cofactors[1], writer, sink, budget, depth + 1)
    elif T == core.AlgebraicArithmeticCertificate:
        ref v = rebind[core.AlgebraicArithmeticCertificate](value)
        _write_node[Int, C, D, E](v.operation, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.left, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.right, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.QQ], C, D, E](v.left_factor, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.QQ], C, D, E](v.right_factor, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.value, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.QQ], C, D, E](v.annihilator, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.QQ], C, D, E](v.value_factor, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.elimination))), sink, budget)
        if v.elimination:
            _write_node[core.ResultantResult[core.QQ], C, D, E](v.elimination.value(), writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.selection))), sink, budget)
        if v.selection:
            _write_node[core.RootInterval, C, D, E](v.selection.value(), writer, sink, budget, depth + 1)
    elif T == core.AlgebraicEvaluationCertificate:
        ref v = rebind[core.AlgebraicEvaluationCertificate](value)
        writer.line(String(len(v.products)), sink, budget)
        for field143 in v.products:
            _write_node[core.AlgebraicArithmeticCertificate, C, D, E](field143, writer, sink, budget, depth + 1)
        writer.line(String(len(v.sums)), sink, budget)
        for field144 in v.sums:
            _write_node[core.AlgebraicArithmeticCertificate, C, D, E](field144, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.value, writer, sink, budget, depth + 1)
    elif T == core.AlgebraicRootsCertificate:
        ref v = rebind[core.AlgebraicRootsCertificate](value)
        writer.line(String(len(v.coefficients)), sink, budget)
        for field171 in v.coefficients:
            _write_node[core.RealAlgebraic, C, D, E](field171, writer, sink, budget, depth + 1)
        writer.line(String(len(v.coefficient_factors)), sink, budget)
        for field172 in v.coefficient_factors:
            _write_node[core.DensePoly[core.QQ], C, D, E](field172, writer, sink, budget, depth + 1)
        writer.line(String(len(v.eliminations)), sink, budget)
        for field173 in v.eliminations:
            _write_node[core.ResultantResult[core.QQ], C, D, E](field173, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.QQ], C, D, E](v.annihilator, writer, sink, budget, depth + 1)
        writer.line(String(len(v.candidates)), sink, budget)
        for field174 in v.candidates:
            _write_node[core.RealAlgebraic, C, D, E](field174, writer, sink, budget, depth + 1)
        writer.line(String(len(v.candidate_factors)), sink, budget)
        for field175 in v.candidate_factors:
            _write_node[core.DensePoly[core.QQ], C, D, E](field175, writer, sink, budget, depth + 1)
        _write_node[core.AlgebraicDescartesCertificate, C, D, E](v.all_roots, writer, sink, budget, depth + 1)
        writer.line(String(len(v.evaluations)), sink, budget)
        for field176 in v.evaluations:
            _write_node[core.AlgebraicEvaluationCertificate, C, D, E](field176, writer, sink, budget, depth + 1)
        writer.line(String(len(v.accepted)), sink, budget)
        for field177 in v.accepted:
            _write_node[Int, C, D, E](field177, writer, sink, budget, depth + 1)
        writer.line(String(len(v.roots)), sink, budget)
        for field178 in v.roots:
            _write_node[core.RealAlgebraic, C, D, E](field178, writer, sink, budget, depth + 1)
        writer.line(String(len(v.filters)), sink, budget)
        for field179 in v.filters:
            _write_node[core.AlgebraicRootFilter, C, D, E](field179, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.element, writer, sink, budget, depth + 1)
        writer.line(String(len(v.representations)), sink, budget)
        for field944 in v.representations:
            _write_node[core.DensePoly[core.QQ], C, D, E](field944, writer, sink, budget, depth + 1)
    elif T == core.AlgebraicRootFilter:
        ref v = rebind[core.AlgebraicRootFilter](value)
        _write_node[Int, C, D, E](v.kind, writer, sink, budget, depth + 1)
        writer.line(String(len(v.coefficients)), sink, budget)
        for field901 in v.coefficients:
            _write_node[core.RealAlgebraic, C, D, E](field901, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.candidate, writer, sink, budget, depth + 1)
        writer.line(String(len(v.representations)), sink, budget)
        for field902 in v.representations:
            _write_node[core.DensePoly[core.QQ], C, D, E](field902, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.element, writer, sink, budget, depth + 1)
    elif T == core.AlgebraicPolynomialEvaluation:
        ref v = rebind[core.AlgebraicPolynomialEvaluation](value)
        writer.line(String(len(v.steps)), sink, budget)
        for field183 in v.steps:
            _write_node[core.AlgebraicArithmeticCertificate, C, D, E](field183, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.value, writer, sink, budget, depth + 1)
        writer.line(String(len(v.witness)), sink, budget)
        for field940 in v.witness:
            _write_node[core.RealAlgebraic, C, D, E](field940, writer, sink, budget, depth + 1)
        writer.line(String(len(v.representations)), sink, budget)
        for field950 in v.representations:
            _write_node[core.DensePoly[core.QQ], C, D, E](field950, writer, sink, budget, depth + 1)
    elif T == core.AlgebraicSpecializationCertificate:
        ref v = rebind[core.AlgebraicSpecializationCertificate](value)
        writer.line(String(len(v.monomials)), sink, budget)
        for field190 in v.monomials:
            _write_node[core.Monomial, C, D, E](field190, writer, sink, budget, depth + 1)
        writer.line(String(len(v.evaluations)), sink, budget)
        for field191 in v.evaluations:
            _write_node[core.AlgebraicPolynomialEvaluation, C, D, E](field191, writer, sink, budget, depth + 1)
    elif T == core.AlgebraicRootsAtCertificate:
        ref v = rebind[core.AlgebraicRootsAtCertificate](value)
        _write_node[core.AlgebraicSpecializationCertificate, C, D, E](v.specialization, writer, sink, budget, depth + 1)
        _write_node[core.AlgebraicRootsCertificate, C, D, E](v.isolation, writer, sink, budget, depth + 1)
    elif T == core.AlgebraicComparisonCertificate:
        ref v = rebind[core.AlgebraicComparisonCertificate](value)
        _write_node[Int, C, D, E](v.relation, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.left, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.right, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.QQ], C, D, E](v.common, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.QQ], C, D, E](v.left_cofactor, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.QQ], C, D, E](v.right_cofactor, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.shared))), sink, budget)
        if v.shared:
            _write_node[core.RootInterval, C, D, E](v.shared.value(), writer, sink, budget, depth + 1)
    elif T == core.CADPolynomialLift:
        ref v = rebind[core.CADPolynomialLift](value)
        writer.line(String(Int(Bool(v.ordinary))), sink, budget)
        if v.ordinary:
            _write_node[core.AlgebraicSpecializationCertificate, C, D, E](v.ordinary.value(), writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.lazard))), sink, budget)
        if v.lazard:
            _write_node[core.LazardEvaluationCertificate, C, D, E](v.lazard.value(), writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.roots))), sink, budget)
        if v.roots:
            _write_node[core.AlgebraicRootsCertificate, C, D, E](v.roots.value(), writer, sink, budget, depth + 1)
    elif T == core.CADStackCertificate:
        ref v = rebind[core.CADStackCertificate](value)
        _write_node[Int, C, D, E](v.parent, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.level, writer, sink, budget, depth + 1)
        writer.line(String(len(v.lifts)), sink, budget)
        for field238 in v.lifts:
            _write_node[core.CADPolynomialLift, C, D, E](field238, writer, sink, budget, depth + 1)
        writer.line(String(len(v.roots)), sink, budget)
        for field239 in v.roots:
            _write_node[core.RealAlgebraic, C, D, E](field239, writer, sink, budget, depth + 1)
        writer.line(String(len(v.sources)), sink, budget)
        for field240 in v.sources:
            _write_node[Int, C, D, E](field240[0], writer, sink, budget, depth + 1)
            _write_node[Int, C, D, E](field240[1], writer, sink, budget, depth + 1)
        writer.line(String(len(v.mapping)), sink, budget)
        for field241 in v.mapping:
            writer.line(String(len(field241)), sink, budget)
            for field242 in field241:
                _write_node[Int, C, D, E](field242, writer, sink, budget, depth + 1)
        writer.line(String(len(v.equalities)), sink, budget)
        for field243 in v.equalities:
            _write_node[core.AlgebraicComparisonCertificate, C, D, E](field243, writer, sink, budget, depth + 1)
        writer.line(String(len(v.ordering)), sink, budget)
        for field244 in v.ordering:
            _write_node[core.AlgebraicComparisonCertificate, C, D, E](field244, writer, sink, budget, depth + 1)
        writer.line(String(len(v.samples)), sink, budget)
        for field245 in v.samples:
            _write_node[core.RealAlgebraic, C, D, E](field245, writer, sink, budget, depth + 1)
        writer.line(String(len(v.separations)), sink, budget)
        for field246 in v.separations:
            _write_node[core.AlgebraicComparisonCertificate, C, D, E](field246, writer, sink, budget, depth + 1)
    elif T == core.CADCell:
        ref v = rebind[core.CADCell](value)
        _write_node[Int, C, D, E](v.parent, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.level, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.position, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.sample, writer, sink, budget, depth + 1)
        writer.line(String(len(v.evaluations)), sink, budget)
        for field257 in v.evaluations:
            _write_node[core.AlgebraicPolynomialEvaluation, C, D, E](field257, writer, sink, budget, depth + 1)
        writer.line(String(len(v.signs)), sink, budget)
        for field258 in v.signs:
            _write_node[core.AlgebraicComparisonCertificate, C, D, E](field258, writer, sink, budget, depth + 1)
        writer.line(String(len(v.witnesses)), sink, budget)
        for field920 in v.witnesses:
            _write_node[core.CADSignWitness, C, D, E](field920, writer, sink, budget, depth + 1)
    elif T == core.CADSignWitness:
        ref v = rebind[core.CADSignWitness](value)
        _write_node[Int, C, D, E](v.kind, writer, sink, budget, depth + 1)
        writer.line(String(len(v.point)), sink, budget)
        for field921 in v.point:
            _write_node[core.RealAlgebraic, C, D, E](field921, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.primitive, writer, sink, budget, depth + 1)
        writer.line(String(len(v.representations)), sink, budget)
        for field922 in v.representations:
            _write_node[core.DensePoly[core.QQ], C, D, E](field922, writer, sink, budget, depth + 1)
    elif T == core.CADCertificate:
        ref v = rebind[core.CADCertificate](value)
        _write_node[core.CADProjectionCertificate, C, D, E](v.projection, writer, sink, budget, depth + 1)
        writer.line(String(len(v.cells)), sink, budget)
        for field266 in v.cells:
            _write_node[core.CADCell, C, D, E](field266, writer, sink, budget, depth + 1)
        writer.line(String(len(v.stacks)), sink, budget)
        for field267 in v.stacks:
            _write_node[core.CADStackCertificate, C, D, E](field267, writer, sink, budget, depth + 1)
    elif T == core.CADCellCertificate:
        ref v = rebind[core.CADCellCertificate](value)
        _write_node[core.CADProjectionCertificate, C, D, E](v.projection, writer, sink, budget, depth + 1)
        writer.line(String(len(v.stacks)), sink, budget)
        for field281 in v.stacks:
            _write_node[core.CADStackCertificate, C, D, E](field281, writer, sink, budget, depth + 1)
        writer.line(String(len(v.positions)), sink, budget)
        for field282 in v.positions:
            _write_node[Int, C, D, E](field282, writer, sink, budget, depth + 1)
        writer.line(String(len(v.evaluations)), sink, budget)
        for field283 in v.evaluations:
            _write_node[core.AlgebraicPolynomialEvaluation, C, D, E](field283, writer, sink, budget, depth + 1)
        writer.line(String(len(v.signs)), sink, budget)
        for field284 in v.signs:
            _write_node[core.AlgebraicComparisonCertificate, C, D, E](field284, writer, sink, budget, depth + 1)
    elif T == core.CADCoveringCertificate:
        ref v = rebind[core.CADCoveringCertificate](value)
        _write_node[core.CADCertificate, C, D, E](v.decomposition, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.witness_cell, writer, sink, budget, depth + 1)
        writer.line(String(len(v.violations)), sink, budget)
        for field290 in v.violations:
            _write_node[Int, C, D, E](field290, writer, sink, budget, depth + 1)
    elif T == core.CADProjectionCertificate:
        ref v = rebind[core.CADProjectionCertificate](value)
        writer.line(String(len(v.variables)), sink, budget)
        for field309 in v.variables:
            _write_node[Int64, C, D, E](field309, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.lazard, writer, sink, budget, depth + 1)
        writer.line(String(len(v.levels)), sink, budget)
        for field310 in v.levels:
            writer.line(String(len(field310)), sink, budget)
            for field311 in field310:
                _write_node[core.SparsePoly[core.QQ], C, D, E](field311, writer, sink, budget, depth + 1)
        writer.line(String(len(v.factorizations)), sink, budget)
        for field312 in v.factorizations:
            _write_node[core.MultivariateFactorization[core.QQ], C, D, E](field312, writer, sink, budget, depth + 1)
        writer.line(String(len(v.resultants)), sink, budget)
        for field313 in v.resultants:
            _write_node[core.ProjectionResultantCertificate, C, D, E](field313, writer, sink, budget, depth + 1)
        writer.line(String(len(v.coprimality)), sink, budget)
        for field314 in v.coprimality:
            _write_node[core.CoprimalityCertificate[core.QQ], C, D, E](field314, writer, sink, budget, depth + 1)
    elif T == core.CADConflict:
        ref v = rebind[core.CADConflict](value)
        _write_node[Int, C, D, E](v.constraint, writer, sink, budget, depth + 1)
        _write_node[core.AlgebraicPolynomialEvaluation, C, D, E](v.evaluation, writer, sink, budget, depth + 1)
        _write_node[core.AlgebraicComparisonCertificate, C, D, E](v.sign, writer, sink, budget, depth + 1)
    elif T == core.CADConflictInterval:
        ref v = rebind[core.CADConflictInterval](value)
        _write_node[Int, C, D, E](v.parent, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.lower, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.upper, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.position, writer, sink, budget, depth + 1)
        _write_node[core.CADConflict, C, D, E](v.proof, writer, sink, budget, depth + 1)
    elif T == core.CylindricalCoveringCertificate:
        ref v = rebind[core.CylindricalCoveringCertificate](value)
        _write_node[core.CADProjectionCertificate, C, D, E](v.projection, writer, sink, budget, depth + 1)
        writer.line(String(len(v.cells)), sink, budget)
        for field336 in v.cells:
            _write_node[core.CADCell, C, D, E](field336, writer, sink, budget, depth + 1)
        writer.line(String(len(v.stacks)), sink, budget)
        for field337 in v.stacks:
            _write_node[core.CADStackCertificate, C, D, E](field337, writer, sink, budget, depth + 1)
        writer.line(String(len(v.conflicts)), sink, budget)
        for field338 in v.conflicts:
            _write_node[core.CADConflictInterval, C, D, E](field338, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.root_conflict))), sink, budget)
        if v.root_conflict:
            _write_node[core.CADConflict, C, D, E](v.root_conflict.value(), writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.witness_cell, writer, sink, budget, depth + 1)
    elif T == core.CoveringBound:
        ref v = rebind[core.CoveringBound](value)
        _write_node[Int, C, D, E](v.polynomial, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.root, writer, sink, budget, depth + 1)
    elif T == core.CoveringInterval:
        ref v = rebind[core.CoveringInterval](value)
        writer.line(String(Int(Bool(v.lower)) + 2 * Int(Bool(v.upper))), sink, budget)
        if v.lower:
            _write_node[core.CoveringBound, C, D, E](v.lower.value(), writer, sink, budget, depth + 1)
        if v.upper:
            _write_node[core.CoveringBound, C, D, E](v.upper.value(), writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.lower_closed, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.upper_closed, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.sample, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.constraint, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.child, writer, sink, budget, depth + 1)
        writer.line(String(len(v.polynomials)), sink, budget)
        for index in v.polynomials:
            _write_node[Int, C, D, E](index, writer, sink, budget, depth + 1)
    elif T == core.CoveringNode:
        ref v = rebind[core.CoveringNode](value)
        _write_node[Int, C, D, E](v.parent, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.interval, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.level, writer, sink, budget, depth + 1)
        writer.line(String(len(v.intervals)), sink, budget)
        for item in v.intervals:
            _write_node[core.CoveringInterval, C, D, E](item, writer, sink, budget, depth + 1)
    elif T == core.CADCoveringsCertificate:
        ref v = rebind[core.CADCoveringsCertificate](value)
        writer.line(String(len(v.variables)), sink, budget)
        for variable in v.variables:
            _write_node[Int64, C, D, E](variable, writer, sink, budget, depth + 1)
        writer.line(String(len(v.polynomials)), sink, budget)
        for f in v.polynomials:
            _write_node[core.SparsePoly[core.QQ], C, D, E](f, writer, sink, budget, depth + 1)
        writer.line(String(len(v.input_factors)), sink, budget)
        for proof in v.input_factors:
            _write_node[core.MultivariateFactorization[core.QQ], C, D, E](proof, writer, sink, budget, depth + 1)
        writer.line(String(len(v.projections)), sink, budget)
        for proof in v.projections:
            _write_node[core.MultivariateFactorization[core.QQ], C, D, E](proof, writer, sink, budget, depth + 1)
        writer.line(String(len(v.nodes)), sink, budget)
        for node in v.nodes:
            _write_node[core.CoveringNode, C, D, E](node, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.root_conflict, writer, sink, budget, depth + 1)
        writer.line(String(len(v.witness)), sink, budget)
        for coordinate in v.witness:
            _write_node[core.RealAlgebraic, C, D, E](coordinate, writer, sink, budget, depth + 1)
        writer.line(String(len(v.evaluations)), sink, budget)
        for evaluation in v.evaluations:
            _write_node[core.AlgebraicPolynomialEvaluation, C, D, E](evaluation, writer, sink, budget, depth + 1)
        writer.line(String(len(v.signs)), sink, budget)
        for sign in v.signs:
            _write_node[core.AlgebraicComparisonCertificate, C, D, E](sign, writer, sink, budget, depth + 1)
    elif T == core.LazardEvaluationCertificate:
        ref v = rebind[core.LazardEvaluationCertificate](value)
        writer.line(String(len(v.orders)), sink, budget)
        for field345 in v.orders:
            _write_node[Int, C, D, E](field345, writer, sink, budget, depth + 1)
        writer.line(String(len(v.evaluations)), sink, budget)
        for field346 in v.evaluations:
            _write_node[core.AlgebraicSpecializationCertificate, C, D, E](field346, writer, sink, budget, depth + 1)
    elif T == core.DeterminantStep:
        ref v = rebind[core.DeterminantStep](value)
        _write_node[Int, C, D, E](v.pivot_row, writer, sink, budget, depth + 1)
        writer.line(String(len(v.trailing)), sink, budget)
        for field353 in v.trailing:
            writer.line(String(len(field353)), sink, budget)
            for field354 in field353:
                _write_node[core.SparsePoly[core.QQ], C, D, E](field354, writer, sink, budget, depth + 1)
    elif T == core.ProjectionResultantCertificate:
        ref v = rebind[core.ProjectionResultantCertificate](value)
        _write_node[Int64, C, D, E](v.variable, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[core.QQ], C, D, E](v.resultant, writer, sink, budget, depth + 1)
        writer.line(String(len(v.steps)), sink, budget)
        for field360 in v.steps:
            _write_node[core.DeterminantStep, C, D, E](field360, writer, sink, budget, depth + 1)
    elif T == core.NumericBox:
        ref v = rebind[core.NumericBox](value)
        _write_node[core.QQ, C, D, E](v.real_low, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.real_high, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.imag_low, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.imag_high, writer, sink, budget, depth + 1)
    elif T == core.RealRootCell:
        ref v = rebind[core.RealRootCell](value)
        _write_node[core.NumericBox, C, D, E](v.interval, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.count, writer, sink, budget, depth + 1)
        _write_node[UInt8, C, D, E](v.method, writer, sink, budget, depth + 1)
        writer.line(String(len(v.evaluations)), sink, budget)
        for field371 in v.evaluations:
            _write_node[core.EnclosureEvaluation[core.BallDomain], C, D, E](field371, writer, sink, budget, depth + 1)
    elif T == core.RealRootResult:
        ref v = rebind[core.RealRootResult](value)
        _write_node[core.NumericOutcome, C, D, E](v.outcome, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.complete, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.accurate, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.isolated, writer, sink, budget, depth + 1)
        writer.line(String(len(v.cells)), sink, budget)
        for field381 in v.cells:
            _write_node[core.RealRootCell, C, D, E](field381, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.sequence))), sink, budget)
        if v.sequence:
            _write_node[core.SturmSequence, C, D, E](v.sequence.value(), writer, sink, budget, depth + 1)
    elif T == core.RootInterval:
        ref v = rebind[core.RootInterval](value)
        _write_node[core.QQ, C, D, E](v.low, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.high, writer, sink, budget, depth + 1)
    elif T == core.DescartesLeaf:
        ref v = rebind[core.DescartesLeaf](value)
        _write_node[core.QQ, C, D, E](v.low, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.high, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.variations, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.resolved, writer, sink, budget, depth + 1)
    elif T == core.DescartesCertificate:
        ref v = rebind[core.DescartesCertificate](value)
        _write_node[core.QQ, C, D, E](v.low, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.high, writer, sink, budget, depth + 1)
        writer.line(String(len(v.leaves)), sink, budget)
        for leaf in v.leaves:
            _write_node[core.DescartesLeaf, C, D, E](leaf, writer, sink, budget, depth + 1)
        writer.line(String(len(v.exact_roots)), sink, budget)
        for root in v.exact_roots:
            _write_node[core.QQ, C, D, E](root, writer, sink, budget, depth + 1)
        writer.line(String(len(v.brackets)), sink, budget)
        for bracket in v.brackets:
            _write_node[core.RootInterval, C, D, E](bracket, writer, sink, budget, depth + 1)
    elif T == core.DescartesRootResult:
        ref v = rebind[core.DescartesRootResult](value)
        _write_node[core.NumericOutcome, C, D, E](v.outcome, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.complete, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.accurate, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.isolated, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.ZZ], C, D, E](v.squarefree, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.ZZ], C, D, E](v.cofactor, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.bound_exponent, writer, sink, budget, depth + 1)
        _write_node[core.DescartesCertificate, C, D, E](v.certificate, writer, sink, budget, depth + 1)
    elif T == core.AlgebraicDescartesCertificate:
        ref v = rebind[core.AlgebraicDescartesCertificate](value)
        _write_node[core.DensePoly[core.ZZ], C, D, E](v.squarefree, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[core.ZZ], C, D, E](v.cofactor, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.bound_exponent, writer, sink, budget, depth + 1)
        _write_node[core.DescartesCertificate, C, D, E](v.certificate, writer, sink, budget, depth + 1)
    elif T == core.ComplexBoundarySegment:
        ref v = rebind[core.ComplexBoundarySegment](value)
        _write_node[core.NumericBox, C, D, E](v.start, writer, sink, budget, depth + 1)
        _write_node[core.NumericBox, C, D, E](v.end, writer, sink, budget, depth + 1)
        _write_node[core.EnclosureEvaluation[core.ComplexBallDomain], C, D, E](v.evaluation, writer, sink, budget, depth + 1)
    elif T == core.ComplexRootRegion:
        ref v = rebind[core.ComplexRootRegion](value)
        _write_node[core.NumericBox, C, D, E](v.rectangle, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.count, writer, sink, budget, depth + 1)
        writer.line(String(len(v.boundary)), sink, budget)
        for field390 in v.boundary:
            _write_node[core.ComplexBoundarySegment, C, D, E](field390, writer, sink, budget, depth + 1)
    elif T == core.ComplexRootResult:
        ref v = rebind[core.ComplexRootResult](value)
        _write_node[core.NumericOutcome, C, D, E](v.outcome, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.complete, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.accurate, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.isolated, writer, sink, budget, depth + 1)
        writer.line(String(len(v.regions)), sink, budget)
        for field398 in v.regions:
            _write_node[core.ComplexRootRegion, C, D, E](field398, writer, sink, budget, depth + 1)
    elif T == core.RootMultiplicityCertificate:
        ref v = rebind[core.RootMultiplicityCertificate](value)
        _write_node[core.SquarefreeDecomposition[core.QQ], C, D, E](v.decomposition, writer, sink, budget, depth + 1)
        writer.line(String(len(v.blocks)), sink, budget)
        for block in v.blocks:
            _write_node[Int, C, D, E](block, writer, sink, budget, depth + 1)
        writer.line(String(len(v.multiplicities)), sink, budget)
        for field413 in v.multiplicities:
            _write_node[Int, C, D, E](field413, writer, sink, budget, depth + 1)
    elif T == core.RootDiagnostics:
        ref v = rebind[core.RootDiagnostics](value)
        _write_node[core.NumericBox, C, D, E](v.residual, writer, sink, budget, depth + 1)
        _write_node[core.NumericBox, C, D, E](v.derivative, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.backward_error_low, writer, sink, budget, depth + 1)
        _write_node[core.QQ, C, D, E](v.backward_error_high, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.newton_correction_upper))), sink, budget)
        if v.newton_correction_upper:
            _write_node[core.QQ, C, D, E](v.newton_correction_upper.value(), writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.coefficient_sensitivity_upper))), sink, budget)
        if v.coefficient_sensitivity_upper:
            _write_node[core.QQ, C, D, E](v.coefficient_sensitivity_upper.value(), writer, sink, budget, depth + 1)
    elif T == core.PolishedRootResult:
        ref v = rebind[core.PolishedRootResult](value)
        _write_node[apn.Complex, C, D, E](v.candidate, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.iterations, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.region))), sink, budget)
        if v.region:
            _write_node[core.ComplexRootRegion, C, D, E](v.region.value(), writer, sink, budget, depth + 1)
        _write_node[core.NumericOutcome, C, D, E](v.outcome, writer, sink, budget, depth + 1)
    elif T == core.NumericDivisionStep:
        ref v = rebind[core.NumericDivisionStep](value)
        _write_node[core.NumericBox, C, D, E](v.quotient, writer, sink, budget, depth + 1)
        writer.line(String(len(v.tail)), sink, budget)
        for field431 in v.tail:
            _write_node[core.NumericBox, C, D, E](field431, writer, sink, budget, depth + 1)
    elif T == core.NumericDivisionResult[D]:
        ref v = rebind[core.NumericDivisionResult[D]](value)
        _write_node[core.NumericDensePoly[D], C, D, E](v.quotient, writer, sink, budget, depth + 1)
        _write_node[core.NumericDensePoly[D], C, D, E](v.remainder, writer, sink, budget, depth + 1)
        writer.line(String(len(v.residual)), sink, budget)
        for field441 in v.residual:
            _write_node[core.NumericBox, C, D, E](field441, writer, sink, budget, depth + 1)
        writer.line(String(len(v.steps)), sink, budget)
        for field442 in v.steps:
            _write_node[core.NumericDivisionStep, C, D, E](field442, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.uniform, writer, sink, budget, depth + 1)
    elif T == core.SparseSquarefreeDecomposition[C]:
        ref v = rebind[core.SparseSquarefreeDecomposition[C]](value)
        _write_node[C, C, D, E](v.unit, writer, sink, budget, depth + 1)
        writer.line(String(len(v.factors)), sink, budget)
        for field449 in v.factors:
            _write_node[core.SparsePoly[C], C, D, E](field449[0], writer, sink, budget, depth + 1)
            _write_node[Int, C, D, E](field449[1], writer, sink, budget, depth + 1)
    elif T == core.MultivariateFactorization[C]:
        ref v = rebind[core.MultivariateFactorization[C]](value)
        _write_node[C, C, D, E](v.unit, writer, sink, budget, depth + 1)
        writer.line(String(len(v.factors)), sink, budget)
        for field456 in v.factors:
            _write_node[core.SparsePoly[C], C, D, E](field456[0], writer, sink, budget, depth + 1)
            _write_node[Int, C, D, E](field456[1], writer, sink, budget, depth + 1)
    elif T == exact._Data[C, E]:
        ref v = rebind[exact._Data[C, E]](value)
        _write_node[core.SparsePoly[C], C, D, E](v.input, writer, sink, budget, depth + 1)
        writer.line(String(len(v.others)), sink, budget)
        for field467 in v.others:
            _write_node[core.SparsePoly[C], C, D, E](field467, writer, sink, budget, depth + 1)
        _write_node[E, C, D, E](v.proof, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.axis, writer, sink, budget, depth + 1)
        writer.line(String(len(v.algebraic_images)), sink, budget)
        for field468 in v.algebraic_images:
            writer.line(String(Int(Bool(field468))), sink, budget)
            if field468:
                _write_node[core.Factorization[C], C, D, E](field468.value(), writer, sink, budget, depth + 1)
    elif T == exact._Interpolation[C]:
        ref v = rebind[exact._Interpolation[C]](value)
        writer.line(String(len(v.points)), sink, budget)
        for field482 in v.points:
            _write_node[C, C, D, E](field482, writer, sink, budget, depth + 1)
        writer.line(String(len(v.values)), sink, budget)
        for field483 in v.values:
            _write_node[C, C, D, E](field483, writer, sink, budget, depth + 1)
        writer.line(String(len(v.jets)), sink, budget)
        for field484 in v.jets:
            writer.line(String(len(field484)), sink, budget)
            for field485 in field484:
                _write_node[C, C, D, E](field485, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.derivatives, writer, sink, budget, depth + 1)
        _write_node[Bool, C, D, E](v.hermite, writer, sink, budget, depth + 1)
    elif T == roots._ExactData:
        ref v = rebind[roots._ExactData](value)
        writer.line(String(len(v.coefficients)), sink, budget)
        for field490 in v.coefficients:
            _write_node[core.RealAlgebraic, C, D, E](field490, writer, sink, budget, depth + 1)
        _write_node[core.AlgebraicRootsCertificate, C, D, E](v.proof, writer, sink, budget, depth + 1)
    elif T == roots._CountData:
        ref v = rebind[roots._CountData](value)
        _write_node[core.DensePoly[core.QQ], C, D, E](v.polynomial, writer, sink, budget, depth + 1)
        _write_node[core.DescartesCountCertificate, C, D, E](v.proof, writer, sink, budget, depth + 1)
    elif T == roots._RealCoverData[_CoreKind[C]]:
        ref v = rebind[roots._RealCoverData[_CoreKind[C]]](value)
        _write_node[core.DensePoly[_common._Ring[_CoreKind[C]]], C, D, E](v.polynomial, writer, sink, budget, depth + 1)
        _write_node[core.NumericOptions, C, D, E](v.options, writer, sink, budget, depth + 1)
        _write_node[core.DescartesRootResult, C, D, E](v.proof, writer, sink, budget, depth + 1)
    elif T == roots._ComplexCoverData[_CoreKind[C]]:
        ref v = rebind[roots._ComplexCoverData[_CoreKind[C]]](value)
        _write_node[core.DensePoly[_common._Ring[_CoreKind[C]]], C, D, E](v.polynomial, writer, sink, budget, depth + 1)
        _write_node[core.NumericOptions, C, D, E](v.options, writer, sink, budget, depth + 1)
        _write_node[core.ComplexRootResult, C, D, E](v.proof, writer, sink, budget, depth + 1)
    elif T == cad._DecompositionData:
        ref v = rebind[cad._DecompositionData](value)
        writer.line(String(len(v.inputs)), sink, budget)
        for field506 in v.inputs:
            _write_node[core.SparsePoly[core.QQ], C, D, E](field506, writer, sink, budget, depth + 1)
        _write_final_cad[C, D, E](v.proof, writer, sink, budget, depth + 1)
        # Scope bits: embedding=1, user bindings=2; preserve legacy 0/1 records.
        writer.line(String(Int(Bool(v.embedding)) + 2 * Int(len(v.fixed) != 0)), sink, budget)
        if v.embedding:
            _write_node[_cad_algebraic._Embedding, C, D, E](v.embedding.value()[], writer, sink, budget, depth + 1)
        if len(v.fixed):
            writer.line(String(len(v.fixed)), sink, budget)
            for binding in v.fixed:
                _write_node[Int, C, D, E](binding[0], writer, sink, budget, depth + 1)
                _write_node[algebraic.Real, C, D, E](binding[1], writer, sink, budget, depth + 1)
    elif T == cad._SolutionData:
        ref v = rebind[cad._SolutionData](value)
        writer.line(String(len(v.inputs)), sink, budget)
        for field517 in v.inputs:
            _write_node[core.SparsePoly[core.QQ], C, D, E](field517, writer, sink, budget, depth + 1)
        writer.line(String(len(v.masks)), sink, budget)
        for field518 in v.masks:
            _write_node[UInt8, C, D, E](field518, writer, sink, budget, depth + 1)
        _write_node[core.CADCoveringsCertificate, C, D, E](v.proof, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.embedding)) + 2 * Int(len(v.fixed) != 0)), sink, budget)
        if v.embedding:
            _write_node[_cad_algebraic._Embedding, C, D, E](v.embedding.value()[], writer, sink, budget, depth + 1)
        if len(v.fixed):
            writer.line(String(len(v.fixed)), sink, budget)
            for binding in v.fixed:
                _write_node[Int, C, D, E](binding[0], writer, sink, budget, depth + 1)
                _write_node[algebraic.Real, C, D, E](binding[1], writer, sink, budget, depth + 1)
    elif T == cad._ProjectionData:
        ref v = rebind[cad._ProjectionData](value)
        writer.line(String(len(v.inputs)), sink, budget)
        for field529 in v.inputs:
            _write_node[core.SparsePoly[core.QQ], C, D, E](field529, writer, sink, budget, depth + 1)
        writer.line(String(len(v.variables)), sink, budget)
        for field530 in v.variables:
            _write_node[Int64, C, D, E](field530, writer, sink, budget, depth + 1)
        _write_node[core.CADProjectionCertificate, C, D, E](v.proof, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.embedding))), sink, budget)
        if v.embedding:
            _write_node[_cad_algebraic._Embedding, C, D, E](v.embedding.value()[], writer, sink, budget, depth + 1)
    elif T == cad._CellAtData:
        ref v = rebind[cad._CellAtData](value)
        writer.line(String(len(v.inputs)), sink, budget)
        for field544 in v.inputs:
            _write_node[core.SparsePoly[core.QQ], C, D, E](field544, writer, sink, budget, depth + 1)
        writer.line(String(len(v.variables)), sink, budget)
        for field545 in v.variables:
            _write_node[Int64, C, D, E](field545, writer, sink, budget, depth + 1)
        writer.line(String(len(v.point)), sink, budget)
        for field546 in v.point:
            _write_node[core.RealAlgebraic, C, D, E](field546, writer, sink, budget, depth + 1)
        _write_node[core.CADCellCertificate, C, D, E](v.proof, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.embedding))), sink, budget)
        if v.embedding:
            _write_node[_cad_algebraic._Embedding, C, D, E](v.embedding.value()[], writer, sink, budget, depth + 1)
    elif T == cad._LazardData:
        ref v = rebind[cad._LazardData](value)
        _write_node[core.SparsePoly[core.QQ], C, D, E](v.polynomial, writer, sink, budget, depth + 1)
        writer.line(String(len(v.point)), sink, budget)
        for field558 in v.point:
            _write_node[Int64, C, D, E](field558[0], writer, sink, budget, depth + 1)
            _write_node[core.RealAlgebraic, C, D, E](field558[1], writer, sink, budget, depth + 1)
        _write_node[Int64, C, D, E](v.axis, writer, sink, budget, depth + 1)
        _write_node[core.LazardEvaluationCertificate, C, D, E](v.proof, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.embedding))), sink, budget)
        if v.embedding:
            _write_node[_cad_algebraic._Embedding, C, D, E](v.embedding.value()[], writer, sink, budget, depth + 1)
    elif T == cad._CoveringData:
        ref v = rebind[cad._CoveringData](value)
        writer.line(String(len(v.inputs)), sink, budget)
        for field569 in v.inputs:
            _write_node[core.SparsePoly[core.QQ], C, D, E](field569, writer, sink, budget, depth + 1)
        writer.line(String(len(v.masks)), sink, budget)
        for field570 in v.masks:
            _write_node[UInt8, C, D, E](field570, writer, sink, budget, depth + 1)
        _write_final_cad[C, D, E](v.proof, writer, sink, budget, depth + 1)
        writer.line(String(Int(Bool(v.embedding)) + 2 * Int(len(v.fixed) != 0)), sink, budget)
        if v.embedding:
            _write_node[_cad_algebraic._Embedding, C, D, E](v.embedding.value()[], writer, sink, budget, depth + 1)
        if len(v.fixed):
            writer.line(String(len(v.fixed)), sink, budget)
            for binding in v.fixed:
                _write_node[Int, C, D, E](binding[0], writer, sink, budget, depth + 1)
                _write_node[algebraic.Real, C, D, E](binding[1], writer, sink, budget, depth + 1)
    elif T == _cad_algebraic._Embedding:
        ref v = rebind[_cad_algebraic._Embedding](value)
        writer.line(String(len(v.originals)), sink, budget)
        for field578 in v.originals:
            _write_node[core.SparsePoly[_algebraic_value.Real], C, D, E](field578, writer, sink, budget, depth + 1)
        writer.line(String(len(v.roots)), sink, budget)
        for field579 in v.roots:
            _write_node[_algebraic_value.Real, C, D, E](field579, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.width, writer, sink, budget, depth + 1)
    elif T == _complex_roots._Data:
        ref v = rebind[_complex_roots._Data](value)
        _write_node[core.DensePoly[_algebraic_value.Complex], C, D, E](v.polynomial, writer, sink, budget, depth + 1)
        _write_node[_complex_roots.ComplexRootsCertificate, C, D, E](v.proof, writer, sink, budget, depth + 1)
    elif T == _complex_roots.ComplexRootsCertificate:
        ref v = rebind[_complex_roots.ComplexRootsCertificate](value)
        writer.line(String(len(v.roots)), sink, budget)
        for field588 in v.roots:
            _write_node[_algebraic_value.Complex, C, D, E](field588, writer, sink, budget, depth + 1)
        writer.line(String(len(v.multiplicities)), sink, budget)
        for field589 in v.multiplicities:
            _write_node[Int, C, D, E](field589, writer, sink, budget, depth + 1)
    elif T == _algebraic_numeric._Witness:
        ref v = rebind[_algebraic_numeric._Witness](value)
        _write_node[core.RealAlgebraic, C, D, E](v.real, writer, sink, budget, depth + 1)
        _write_node[core.RealAlgebraic, C, D, E](v.imag, writer, sink, budget, depth + 1)
    elif T == _rational_field.RationalFunction[F]:
        ref v = rebind[_rational_field.RationalFunction[F]](value)
        _write_node[core.SparsePoly[F], C, D, E](v.numerator, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[F], C, D, E](v.denominator, writer, sink, budget, depth + 1)
    elif T == _rational_field.Cancellation[F]:
        ref v = rebind[_rational_field.Cancellation[F]](value)
        _write_node[core.SparsePoly[F], C, D, E](v.common, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[F], C, D, E](v.cofactors[0], writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[F], C, D, E](v.cofactors[1], writer, sink, budget, depth + 1)
    elif T == _rational_field.PartialFractionTerm[F]:
        ref v = rebind[_rational_field.PartialFractionTerm[F]](value)
        _write_node[core.DensePoly[F], C, D, E](v.numerator, writer, sink, budget, depth + 1)
        _write_node[core.DensePoly[F], C, D, E](v.factor, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.exponent, writer, sink, budget, depth + 1)
    elif T == _rational_field.LaurentExpansion[F]:
        ref v = rebind[_rational_field.LaurentExpansion[F]](value)
        _write_node[Int64, C, D, E](v.variable, writer, sink, budget, depth + 1)
        _write_node[F, C, D, E](v.center, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.valuation, writer, sink, budget, depth + 1)
        writer.line(String(len(v.coefficients)), sink, budget)
        for field607 in v.coefficients:
            _write_node[F, C, D, E](field607, writer, sink, budget, depth + 1)
    elif T == _rational_certificates._Irreducibility:
        ref v = rebind[_rational_certificates._Irreducibility](value)
        _write_node[UInt64, C, D, E](v.prime, writer, sink, budget, depth + 1)
        _write_node[Int, C, D, E](v.shift, writer, sink, budget, depth + 1)
    elif T == _rational_certificates._Factors[F]:
        ref v = rebind[_rational_certificates._Factors[F]](value)
        _write_node[core.Factorization[F], C, D, E](v.value, writer, sink, budget, depth + 1)
        writer.line(String(len(v.certificates)), sink, budget)
        for field614 in v.certificates:
            _write_node[_rational_certificates._Irreducibility, C, D, E](field614, writer, sink, budget, depth + 1)
    elif T == _determinant.Step[C]:
        ref v = rebind[_determinant.Step[C]](value)
        _write_node[Int, C, D, E](v.pivot_row, writer, sink, budget, depth + 1)
        writer.line(String(len(v.trailing)), sink, budget)
        for field621 in v.trailing:
            writer.line(String(len(field621)), sink, budget)
            for field622 in field621:
                _write_node[core.SparsePoly[C], C, D, E](field622, writer, sink, budget, depth + 1)
    elif T == _determinant.Certificate[C]:
        ref v = rebind[_determinant.Certificate[C]](value)
        _write_node[Int64, C, D, E](v.variable, writer, sink, budget, depth + 1)
        _write_node[core.SparsePoly[C], C, D, E](v.resultant, writer, sink, budget, depth + 1)
        writer.line(String(len(v.steps)), sink, budget)
        for field628 in v.steps:
            _write_node[_determinant.Step[C], C, D, E](field628, writer, sink, budget, depth + 1)
    elif T == algebraic._SpecializationData:
        ref v = rebind[algebraic._SpecializationData](value)
        _write_node[core.SparsePoly[core.QQ], C, D, E](v.polynomial, writer, sink, budget, depth + 1)
        writer.line(String(len(v.point)), sink, budget)
        for field636 in v.point:
            _write_node[Int64, C, D, E](field636[0], writer, sink, budget, depth + 1)
            _write_node[core.RealAlgebraic, C, D, E](field636[1], writer, sink, budget, depth + 1)
        _write_node[core.AlgebraicSpecializationCertificate, C, D, E](v.proof, writer, sink, budget, depth + 1)
    elif T == _algebraic_numeric._Polynomial[core.ComplexBallDomain, False]:
        ref v = rebind[_algebraic_numeric._Polynomial[core.ComplexBallDomain, False]](value)
        _write_node[core.NumericDensePoly[core.ComplexBallDomain], C, D, E](v.value, writer, sink, budget, depth + 1)
        writer.line(String(len(v.witnesses)), sink, budget)
        for field641 in v.witnesses:
            _write_node[_algebraic_numeric._Witness, C, D, E](field641, writer, sink, budget, depth + 1)
    elif T == _algebraic_numeric._Polynomial[D, False]:
        ref v = rebind[_algebraic_numeric._Polynomial[D, False]](value)
        _write_node[core.NumericDensePoly[D], C, D, E](v.value, writer, sink, budget, depth + 1)
        writer.line(String(len(v.witnesses)), sink, budget)
        for witness in v.witnesses:
            _write_node[_algebraic_numeric._Witness, C, D, E](witness, writer, sink, budget, depth + 1)
    elif T == _algebraic_numeric._Polynomial[D, True]:
        ref v = rebind[_algebraic_numeric._Polynomial[D, True]](value)
        _write_node[core.NumericSparsePoly[D], C, D, E](v.value, writer, sink, budget, depth + 1)
        writer.line(String(len(v.witnesses)), sink, budget)
        for witness in v.witnesses:
            _write_node[_algebraic_numeric._Witness, C, D, E](witness, writer, sink, budget, depth + 1)
    elif T == core.EnclosureEvaluation[D]:
        ref v = rebind[core.EnclosureEvaluation[D]](value)
        _write_node[Int, C, D, E](v.precision, writer, sink, budget, depth + 1)
        writer.line(String(len(v._value)), sink, budget)
        for field649 in v._value:
            _write_node[D.Scalar, C, D, E](field649, writer, sink, budget, depth + 1)
        writer.line(String(len(v.steps)), sink, budget)
        for field650 in v.steps:
            _write_node[core.NumericBox, C, D, E](field650, writer, sink, budget, depth + 1)
    elif T == core.AdaptiveEvaluation[D]:
        ref v = rebind[core.AdaptiveEvaluation[D]](value)
        _write_node[core.NumericOutcome, C, D, E](v.outcome, writer, sink, budget, depth + 1)
        _write_node[core.EnclosureEvaluation[D], C, D, E](v.evaluation, writer, sink, budget, depth + 1)
    else:
        comptime assert False, "unsupported certificate node"


def _read_node[T: Copyable & Deinitable, C: CoefficientRing, D: NumericDomain, E: Copyable & Deinitable, S: PolynomialTextSource](mut reader: _Reader[S], mut budget: Budget, depth: Int) raises PolyError -> T:
    _depth(depth, budget)
    comptime F = downcast[C, CoefficientField] if conforms_to(C, CoefficientField) else core.QQ
    comptime if (T == core.NumericDensePoly[core.FloatDomain] or T == core.NumericSparsePoly[core.FloatDomain] or T == core.EnclosureEvaluation[core.FloatDomain] or T == core.AdaptiveEvaluation[core.FloatDomain]) and D != core.FloatDomain:
        return _read_node[T, C, core.FloatDomain, E](reader, budget, depth + 1)
    elif (T == core.NumericDensePoly[core.ComplexDomain] or T == core.NumericSparsePoly[core.ComplexDomain] or T == core.EnclosureEvaluation[core.ComplexDomain] or T == core.AdaptiveEvaluation[core.ComplexDomain]) and D != core.ComplexDomain:
        return _read_node[T, C, core.ComplexDomain, E](reader, budget, depth + 1)
    elif (T == core.NumericDensePoly[core.BallDomain] or T == core.NumericSparsePoly[core.BallDomain] or T == core.EnclosureEvaluation[core.BallDomain] or T == core.AdaptiveEvaluation[core.BallDomain]) and D != core.BallDomain:
        return _read_node[T, C, core.BallDomain, E](reader, budget, depth + 1)
    elif (T == core.NumericDensePoly[core.ComplexBallDomain] or T == core.NumericSparsePoly[core.ComplexBallDomain] or T == core.EnclosureEvaluation[core.ComplexBallDomain] or T == core.AdaptiveEvaluation[core.ComplexBallDomain]) and D != core.ComplexBallDomain:
        return _read_node[T, C, core.ComplexBallDomain, E](reader, budget, depth + 1)
    elif (T == core.DensePoly[core.QQ] or T == core.SparsePoly[core.QQ]) and C != core.QQ:
        return _read_node[T, core.QQ, D, E](reader, budget, depth + 1)
    elif (T == core.DensePoly[core.ZZ] or T == core.SparsePoly[core.ZZ]) and C != core.ZZ:
        return _read_node[T, core.ZZ, D, E](reader, budget, depth + 1)
    elif (T == core.DensePoly[core.QQi] or T == core.SparsePoly[core.QQi]) and C != core.QQi:
        return _read_node[T, core.QQi, D, E](reader, budget, depth + 1)
    elif (T == core.DensePoly[_algebraic_value.Real] or T == core.SparsePoly[_algebraic_value.Real]) and C != _algebraic_value.Real:
        return _read_node[T, _algebraic_value.Real, D, E](reader, budget, depth + 1)
    elif (T == core.DensePoly[_algebraic_value.Complex] or T == core.SparsePoly[_algebraic_value.Complex]) and C != _algebraic_value.Complex:
        return _read_node[T, _algebraic_value.Complex, D, E](reader, budget, depth + 1)
    elif (T == core.DensePoly[core.ModInt] or T == core.SparsePoly[core.ModInt]) and C != core.ModInt:
        return _read_node[T, core.ModInt, D, E](reader, budget, depth + 1)
    elif conforms_to(T, _Archive):
        return rebind_var[T](downcast[T, _Archive]._archive_read(reader, budget, depth))
    elif conforms_to(T, _Record) or _value_io._Supported[T]:
        return _value_io._read[T](reader, budget)
    elif conforms_to(T, sparse._Powers):
        var monomial = _read_node[core.Monomial, C, D, E](reader, budget, depth + 1)
        for pair in monomial.pairs:
            budget.charge(1)
            if pair[0] < 0 or pair[0] >= Int64(sparse._width[T]()):
                raise PolyError(PolyErrorKind.ENCODING, "archived power is outside the tuple shape")
        return sparse._powers[T](monomial)
    elif T == Int:
        return rebind_var[T](Int(reader.identifier(budget)))
    elif T == Int64:
        return rebind_var[T](Int64(reader.identifier(budget)))
    elif T == UInt64:
        return rebind_var[T](UInt64(reader.number(UInt64(UInt64.MAX), budget)))
    elif T == UInt32:
        return rebind_var[T](UInt32(reader.number(UInt64(UInt32.MAX), budget)))
    elif T == UInt8:
        return rebind_var[T](UInt8(reader.number(UInt64(UInt8.MAX), budget)))
    elif T == Bool:
        return rebind_var[T](Bool(reader.number(1, budget)))
    elif T == core.NoContext:
        return rebind_var[T](core.NoContext())
    elif T == core.Modulus:
        return rebind_var[T](core.Modulus(reader.number(UInt64.MAX, budget), budget))
    elif T == core.QQ:
        return rebind_var[T](reader.rational(budget))
    elif T == core.ZZ:
        return rebind_var[T](core.ZZ(_value_io._read[apn.Integer](reader, budget)))
    elif T == core.QQi:
        return rebind_var[T](core.QQi(_value_io._read[apn.ExactComplex](reader, budget)))
    elif T == core.RealAlgebraic:
        var value = reader.real(budget)
        return rebind_var[T](_algebraic_value._copy_witness(value.witness(), budget))
    elif T == core.NumericOutcome:
        return rebind_var[T](core.NumericOutcome(UInt8(reader.number(5, budget))))
    elif T == core.Monomial:
        var field2 = reader.count(budget)
        var field1 = List[Tuple[Int64, UInt32]]()
        for _ in range(field2):
            var field4 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
            var field5 = _read_node[UInt32, C, D, E](reader, budget, depth + 1)
            var field3 = (field4, field5)
            _grow(field1, budget)
            field1.append(field3^)
        var result = core.Monomial(field1^, budget)
        return rebind_var[T](result^)
    elif T == core.MonomialOrder:
        var field7 = _read_node[UInt8, C, D, E](reader, budget, depth + 1)
        var field9 = reader.count(budget)
        var field8 = List[Int64]()
        for _ in range(field9):
            var field10 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
            _grow(field8, budget)
            field8.append(field10)
        var result = core.MonomialOrder(field7, field8^, budget)
        return rebind_var[T](result^)
    elif T == core.DensePoly[C]:
        var field12 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
        var field13 = _read_node[C.Context, C, D, E](reader, budget, depth + 1)
        var field15 = reader.count(budget)
        var field14 = List[C]()
        for _ in range(field15):
            var field16 = _read_node[C, C, D, E](reader, budget, depth + 1)
            _grow(field14, budget)
            field14.append(field16^)
        var result = core.DensePoly[C](field12, field13^)
        result.coefficients = field14^
        result.check_invariants(budget)
        return rebind_var[T](result^)
    elif T == core.Term[C]:
        var field18 = _read_node[core.Monomial, C, D, E](reader, budget, depth + 1)
        var field19 = _read_node[C, C, D, E](reader, budget, depth + 1)
        var result = core.Term[C](field18^, field19^)
        return rebind_var[T](result^)
    elif T == core.SparsePoly[C]:
        var field20 = _read_node[core.MonomialOrder, C, D, E](reader, budget, depth + 1)
        var field21 = _read_node[C.Context, C, D, E](reader, budget, depth + 1)
        var field23 = reader.count(budget)
        var field22 = List[core.Term[C]]()
        for _ in range(field23):
            var field24 = _read_node[core.Term[C], C, D, E](reader, budget, depth + 1)
            _grow(field22, budget)
            field22.append(field24^)
        var result = core.SparsePoly[C](field20^, field21^)
        result.terms = field22^
        result.check_invariants(budget)
        return rebind_var[T](result^)
    elif T == core.NumericDensePoly[D]:
        var field26 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
        var field28 = reader.count(budget)
        var field27 = List[D.Scalar]()
        for _ in range(field28):
            var field29 = _read_node[D.Scalar, C, D, E](reader, budget, depth + 1)
            _grow(field27, budget)
            field27.append(field29^)
        var result = core.NumericDensePoly[D](field26)
        result.coefficients = field27^
        for coefficient in result.coefficients:
            _ = core.numeric_bounds[D](coefficient, budget)
        if len(result.coefficients) and _value_io._zero(result.coefficients[len(result.coefficients) - 1], budget):
            raise _bad("noncanonical numerical polynomial")
        return rebind_var[T](result^)
    elif T == core.NumericTerm[D]:
        var field31 = _read_node[core.Monomial, C, D, E](reader, budget, depth + 1)
        var field32 = _read_node[D.Scalar, C, D, E](reader, budget, depth + 1)
        var result = core.NumericTerm[D](field31^, field32^)
        return rebind_var[T](result^)
    elif T == core.NumericSparsePoly[D]:
        var field33 = _read_node[core.MonomialOrder, C, D, E](reader, budget, depth + 1)
        var field35 = reader.count(budget)
        var field34 = List[core.NumericTerm[D]]()
        for _ in range(field35):
            var field36 = _read_node[core.NumericTerm[D], C, D, E](reader, budget, depth + 1)
            _grow(field34, budget)
            field34.append(field36^)
        var result = core.NumericSparsePoly[D](field33^)
        result.terms = field34^
        for i in range(len(result.terms)):
            ref term = result.terms[i]
            term.monomial.check_invariants(budget)
            _ = core.numeric_bounds[D](term.coefficient, budget)
            if _value_io._zero(term.coefficient, budget) or (i and result.order.compare(result.terms[i-1].monomial, term.monomial, budget) >= 0):
                raise _bad("noncanonical numerical sparse polynomial")
        return rebind_var[T](result^)
    elif T == core.NumericOptions:
        var field38 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field39 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field40 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field41 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field42 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field43 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var result = core.NumericOptions(initial_precision=field38, max_precision=field39, absolute_bits=field40, relative_bits=field41, max_subdivisions=field42, require_isolation=field43)
        return rebind_var[T](result^)
    elif T == core.MembershipCertificate[C]:
        var field45 = reader.count(budget)
        var field44 = List[core.SparsePoly[C]]()
        for _ in range(field45):
            var field46 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
            _grow(field44, budget)
            field44.append(field46^)
        return rebind_var[T](core.MembershipCertificate[C](field44^))
    elif T == core.SquarefreeDecomposition[C]:
        var field48 = _read_node[C, C, D, E](reader, budget, depth + 1)
        var field50 = reader.count(budget)
        var field49 = List[Tuple[core.DensePoly[C], Int]]()
        for _ in range(field50):
            var field52 = _read_node[core.DensePoly[C], C, D, E](reader, budget, depth + 1)
            var field53 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            var field51 = (field52^, field53)
            _grow(field49, budget)
            field49.append(field51^)
        return rebind_var[T](core.SquarefreeDecomposition[C](field48^, field49^))
    elif T == core.Factorization[C]:
        var field55 = _read_node[C, C, D, E](reader, budget, depth + 1)
        var field57 = reader.count(budget)
        var field56 = List[Tuple[core.DensePoly[C], Int]]()
        for _ in range(field57):
            var field59 = _read_node[core.DensePoly[C], C, D, E](reader, budget, depth + 1)
            var field60 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            var field58 = (field59^, field60)
            _grow(field56, budget)
            field56.append(field58^)
        return rebind_var[T](core.Factorization[C](field55^, field56^))
    elif T == core.DivisionResult[C]:
        var field62 = _read_node[core.DensePoly[C], C, D, E](reader, budget, depth + 1)
        var field63 = _read_node[core.DensePoly[C], C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.DivisionResult[C](field62^, field63^))
    elif T == core.ListDivision[C]:
        var field65 = reader.count(budget)
        var field64 = List[core.SparsePoly[C]]()
        for _ in range(field65):
            var field66 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
            _grow(field64, budget)
            field64.append(field66^)
        var field67 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.ListDivision[C](field64^, field67^))
    elif T == core.ContentGcdStep[C]:
        var field69 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field71 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field72 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field70 = (field71^, field72^)
        var field73 = Optional[Int]()
        if reader.number(1, budget):
            var field74 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            field73 = field74
        return rebind_var[T](core.ContentGcdStep[C](field69^, field70^, field73^))
    elif T == core.CoprimalityNode[C]:
        var field75 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
        var field76 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field77 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field78 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field80 = reader.count(budget)
        var field79 = List[core.ContentGcdStep[C]]()
        for _ in range(field80):
            var field81 = _read_node[core.ContentGcdStep[C], C, D, E](reader, budget, depth + 1)
            _grow(field79, budget)
            field79.append(field81^)
        var field83 = reader.count(budget)
        var field82 = List[core.ContentGcdStep[C]]()
        for _ in range(field83):
            var field84 = _read_node[core.ContentGcdStep[C], C, D, E](reader, budget, depth + 1)
            _grow(field82, budget)
            field82.append(field84^)
        var field85 = Optional[Int]()
        if reader.number(1, budget):
            var field86 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            field85 = field86
        return rebind_var[T](core.CoprimalityNode[C](field75, field76^, field77^, field78^, field79^, field82^, field85^))
    elif T == core.CoprimalityCertificate[C]:
        var field90 = reader.count(budget)
        var field89 = List[core.CoprimalityNode[C]]()
        for _ in range(field90):
            var field91 = _read_node[core.CoprimalityNode[C], C, D, E](reader, budget, depth + 1)
            _grow(field89, budget)
            field89.append(field91^)
        var field92 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.CoprimalityCertificate[C](field89^, field92))
    elif T == core.GcdResult[C]:
        var field94 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field96 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field97 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field95 = (field96^, field97^)
        var field98 = Optional[Tuple[core.SparsePoly[C], core.SparsePoly[C]]]()
        if reader.number(1, budget):
            var field100 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
            var field101 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
            var field99 = (field100^, field101^)
            field98 = field99^
        var field102 = Optional[core.CoprimalityCertificate[C]]()
        if reader.number(1, budget):
            var field103 = _read_node[core.CoprimalityCertificate[C], C, D, E](reader, budget, depth + 1)
            field102 = field103^
        return rebind_var[T](core.GcdResult[C](field94^, field95^, field98^, field102^))
    elif T == core.ResultantResult[C]:
        var field104 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field106 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field107 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field105 = (field106^, field107^)
        return rebind_var[T](core.ResultantResult[C](field104^, field105^))
    elif T == core.SturmSequence:
        var field109 = reader.count(budget)
        var field108 = List[core.DensePoly[core.QQ]]()
        for _ in range(field109):
            var field110 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field108, budget)
            field108.append(field110^)
        var field112 = reader.count(budget)
        var field111 = List[core.DensePoly[core.QQ]]()
        for _ in range(field112):
            var field113 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field111, budget)
            field111.append(field113^)
        return rebind_var[T](core.SturmSequence(field108^, field111^))
    elif T == core.DescartesCountCertificate:
        var isolation = _read_node[core.AlgebraicDescartesCertificate, C, D, E](reader, budget, depth + 1)
        var low = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var high = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var count = _read_node[Int, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.DescartesCountCertificate(isolation^, low^, high^, count))
    elif T == core.RootCountCertificate:
        var field116 = _read_node[core.SturmSequence, C, D, E](reader, budget, depth + 1)
        var field117 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var field118 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var field119 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.RootCountCertificate(field116^, field117^, field118^, field119))
    elif T == core.CancellationCertificate:
        var field120 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field122 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field123 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field121 = (field122^, field123^)
        return rebind_var[T](core.CancellationCertificate(field120^, field121^))
    elif T == core.AlgebraicArithmeticCertificate:
        var field124 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field125 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field126 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field127 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field128 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field129 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field130 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field131 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field132 = Optional[core.ResultantResult[core.QQ]]()
        if reader.number(1, budget):
            var field133 = _read_node[core.ResultantResult[core.QQ], C, D, E](reader, budget, depth + 1)
            field132 = field133^
        var field134 = Optional[core.RootInterval]()
        if reader.number(1, budget):
            var field135 = _read_node[core.RootInterval, C, D, E](reader, budget, depth + 1)
            field134 = field135^
        return rebind_var[T](core.AlgebraicArithmeticCertificate(field124, field125^, field126^, field127^, field128^, field129^, field130^, field131^, field132^, field134^))
    elif T == core.AlgebraicEvaluationCertificate:
        var field137 = reader.count(budget)
        var field136 = List[core.AlgebraicArithmeticCertificate]()
        for _ in range(field137):
            var field138 = _read_node[core.AlgebraicArithmeticCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field136, budget)
            field136.append(field138^)
        var field140 = reader.count(budget)
        var field139 = List[core.AlgebraicArithmeticCertificate]()
        for _ in range(field140):
            var field141 = _read_node[core.AlgebraicArithmeticCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field139, budget)
            field139.append(field141^)
        var field142 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.AlgebraicEvaluationCertificate(field136^, field139^, field142^))
    elif T == core.AlgebraicRootsCertificate:
        var field146 = reader.count(budget)
        var field145 = List[core.RealAlgebraic]()
        for _ in range(field146):
            var field147 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field145, budget)
            field145.append(field147^)
        var field149 = reader.count(budget)
        var field148 = List[core.DensePoly[core.QQ]]()
        for _ in range(field149):
            var field150 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field148, budget)
            field148.append(field150^)
        var field152 = reader.count(budget)
        var field151 = List[core.ResultantResult[core.QQ]]()
        for _ in range(field152):
            var field153 = _read_node[core.ResultantResult[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field151, budget)
            field151.append(field153^)
        var field154 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field156 = reader.count(budget)
        var field155 = List[core.RealAlgebraic]()
        for _ in range(field156):
            var field157 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field155, budget)
            field155.append(field157^)
        var field159 = reader.count(budget)
        var field158 = List[core.DensePoly[core.QQ]]()
        for _ in range(field159):
            var field160 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field158, budget)
            field158.append(field160^)
        var field161 = _read_node[core.AlgebraicDescartesCertificate, C, D, E](reader, budget, depth + 1)
        var field163 = reader.count(budget)
        var field162 = List[core.AlgebraicEvaluationCertificate]()
        for _ in range(field163):
            var field164 = _read_node[core.AlgebraicEvaluationCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field162, budget)
            field162.append(field164^)
        var field166 = reader.count(budget)
        var field165 = List[Int]()
        for _ in range(field166):
            var field167 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            _grow(field165, budget)
            field165.append(field167)
        var field169 = reader.count(budget)
        var field168 = List[core.RealAlgebraic]()
        for _ in range(field169):
            var field170 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field168, budget)
            field168.append(field170^)
        var field904 = reader.count(budget)
        var field903 = List[core.AlgebraicRootFilter]()
        for _ in range(field904):
            var field905 = _read_node[core.AlgebraicRootFilter, C, D, E](reader, budget, depth + 1)
            _grow(field903, budget)
            field903.append(field905^)
        var field945 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field947 = reader.count(budget)
        var field946 = List[core.DensePoly[core.QQ]]()
        for _ in range(field947):
            var field948 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field946, budget)
            field946.append(field948^)
        return rebind_var[T](core.AlgebraicRootsCertificate(field145^, field148^, field151^, field154^, field155^, field158^, field161^, field162^, field165^, field168^, field903^, field945^, field946^))
    elif T == core.AlgebraicRootFilter:
        var field906 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field908 = reader.count(budget)
        var field907 = List[core.RealAlgebraic]()
        for _ in range(field908):
            var field909 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field907, budget)
            field907.append(field909^)
        var field910 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field912 = reader.count(budget)
        var field911 = List[core.DensePoly[core.QQ]]()
        for _ in range(field912):
            var field913 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field911, budget)
            field911.append(field913^)
        var field914 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.AlgebraicRootFilter(field906, field907^, field910^, field911^, field914^))
    elif T == core.AlgebraicPolynomialEvaluation:
        var field180 = reader.count(budget)
        var field179 = List[core.AlgebraicArithmeticCertificate]()
        for _ in range(field180):
            var field181 = _read_node[core.AlgebraicArithmeticCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field179, budget)
            field179.append(field181^)
        var field182 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field942 = reader.count(budget)
        var field941 = List[core.RealAlgebraic]()
        for _ in range(field942):
            var field943 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field941, budget)
            field941.append(field943^)
        var field952 = reader.count(budget)
        var field951 = List[core.DensePoly[core.QQ]]()
        for _ in range(field952):
            var field953 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field951, budget)
            field951.append(field953^)
        return rebind_var[T](core.AlgebraicPolynomialEvaluation(field179^, field182^, field941^, field951^))
    elif T == core.AlgebraicSpecializationCertificate:
        var field185 = reader.count(budget)
        var field184 = List[core.Monomial]()
        for _ in range(field185):
            var field186 = _read_node[core.Monomial, C, D, E](reader, budget, depth + 1)
            _grow(field184, budget)
            field184.append(field186^)
        var field188 = reader.count(budget)
        var field187 = List[core.AlgebraicPolynomialEvaluation]()
        for _ in range(field188):
            var field189 = _read_node[core.AlgebraicPolynomialEvaluation, C, D, E](reader, budget, depth + 1)
            _grow(field187, budget)
            field187.append(field189^)
        return rebind_var[T](core.AlgebraicSpecializationCertificate(field184^, field187^))
    elif T == core.AlgebraicRootsAtCertificate:
        var field192 = _read_node[core.AlgebraicSpecializationCertificate, C, D, E](reader, budget, depth + 1)
        var field193 = _read_node[core.AlgebraicRootsCertificate, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.AlgebraicRootsAtCertificate(field192^, field193^))
    elif T == core.AlgebraicComparisonCertificate:
        var field194 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field195 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field196 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field197 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field198 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field199 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field200 = Optional[core.RootInterval]()
        if reader.number(1, budget):
            var field201 = _read_node[core.RootInterval, C, D, E](reader, budget, depth + 1)
            field200 = field201^
        return rebind_var[T](core.AlgebraicComparisonCertificate(field194, field195^, field196^, field197^, field198^, field199^, field200^))
    elif T == core.CADPolynomialLift:
        var field202 = Optional[core.AlgebraicSpecializationCertificate]()
        if reader.number(1, budget):
            var field203 = _read_node[core.AlgebraicSpecializationCertificate, C, D, E](reader, budget, depth + 1)
            field202 = field203^
        var field204 = Optional[core.LazardEvaluationCertificate]()
        if reader.number(1, budget):
            var field205 = _read_node[core.LazardEvaluationCertificate, C, D, E](reader, budget, depth + 1)
            field204 = field205^
        var field206 = Optional[core.AlgebraicRootsCertificate]()
        if reader.number(1, budget):
            var field207 = _read_node[core.AlgebraicRootsCertificate, C, D, E](reader, budget, depth + 1)
            field206 = field207^
        return rebind_var[T](core.CADPolynomialLift(field202^, field204^, field206^))
    elif T == core.CADStackCertificate:
        var field208 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field209 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field211 = reader.count(budget)
        var field210 = List[core.CADPolynomialLift]()
        for _ in range(field211):
            var field212 = _read_node[core.CADPolynomialLift, C, D, E](reader, budget, depth + 1)
            _grow(field210, budget)
            field210.append(field212^)
        var field214 = reader.count(budget)
        var field213 = List[core.RealAlgebraic]()
        for _ in range(field214):
            var field215 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field213, budget)
            field213.append(field215^)
        var field217 = reader.count(budget)
        var field216 = List[Tuple[Int, Int]]()
        for _ in range(field217):
            var field219 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            var field220 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            var field218 = (field219, field220)
            _grow(field216, budget)
            field216.append(field218^)
        var field222 = reader.count(budget)
        var field221 = List[List[Int]]()
        for _ in range(field222):
            var field224 = reader.count(budget)
            var field223 = List[Int]()
            for _ in range(field224):
                var field225 = _read_node[Int, C, D, E](reader, budget, depth + 1)
                _grow(field223, budget)
                field223.append(field225)
            _grow(field221, budget)
            field221.append(field223^)
        var field227 = reader.count(budget)
        var field226 = List[core.AlgebraicComparisonCertificate]()
        for _ in range(field227):
            var field228 = _read_node[core.AlgebraicComparisonCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field226, budget)
            field226.append(field228^)
        var field230 = reader.count(budget)
        var field229 = List[core.AlgebraicComparisonCertificate]()
        for _ in range(field230):
            var field231 = _read_node[core.AlgebraicComparisonCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field229, budget)
            field229.append(field231^)
        var field233 = reader.count(budget)
        var field232 = List[core.RealAlgebraic]()
        for _ in range(field233):
            var field234 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field232, budget)
            field232.append(field234^)
        var field236 = reader.count(budget)
        var field235 = List[core.AlgebraicComparisonCertificate]()
        for _ in range(field236):
            var field237 = _read_node[core.AlgebraicComparisonCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field235, budget)
            field235.append(field237^)
        return rebind_var[T](core.CADStackCertificate(field208, field209, field210^, field213^, field216^, field221^, field226^, field229^, field232^, field235^))
    elif T == core.CADCell:
        var field247 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field248 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field249 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field250 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field252 = reader.count(budget)
        var field251 = List[core.AlgebraicPolynomialEvaluation]()
        for _ in range(field252):
            var field253 = _read_node[core.AlgebraicPolynomialEvaluation, C, D, E](reader, budget, depth + 1)
            _grow(field251, budget)
            field251.append(field253^)
        var field255 = reader.count(budget)
        var field254 = List[core.AlgebraicComparisonCertificate]()
        for _ in range(field255):
            var field256 = _read_node[core.AlgebraicComparisonCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field254, budget)
            field254.append(field256^)
        var field924 = reader.count(budget)
        var field923 = List[core.CADSignWitness]()
        for _ in range(field924):
            var field925 = _read_node[core.CADSignWitness, C, D, E](reader, budget, depth + 1)
            _grow(field923, budget)
            field923.append(field925^)
        return rebind_var[T](core.CADCell(field247, field248, field249, field250^, field251^, field254^, field923^))
    elif T == core.CADSignWitness:
        var field926 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field928 = reader.count(budget)
        var field927 = List[core.RealAlgebraic]()
        for _ in range(field928):
            var field929 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field927, budget)
            field927.append(field929^)
        var field930 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field932 = reader.count(budget)
        var field931 = List[core.DensePoly[core.QQ]]()
        for _ in range(field932):
            var field933 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field931, budget)
            field931.append(field933^)
        return rebind_var[T](core.CADSignWitness(field926, field927^, field930, field931^))
    elif T == core.CADCertificate:
        var field259 = _read_node[core.CADProjectionCertificate, C, D, E](reader, budget, depth + 1)
        var field261 = reader.count(budget)
        var field260 = List[core.CADCell]()
        for _ in range(field261):
            var field262 = _read_node[core.CADCell, C, D, E](reader, budget, depth + 1)
            _grow(field260, budget)
            field260.append(field262^)
        var field264 = reader.count(budget)
        var field263 = List[core.CADStackCertificate]()
        for _ in range(field264):
            var field265 = _read_node[core.CADStackCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field263, budget)
            field263.append(field265^)
        return rebind_var[T](core.CADCertificate(field259^, field260^, field263^))
    elif T == core.CADCellCertificate:
        var field268 = _read_node[core.CADProjectionCertificate, C, D, E](reader, budget, depth + 1)
        var field270 = reader.count(budget)
        var field269 = List[core.CADStackCertificate]()
        for _ in range(field270):
            var field271 = _read_node[core.CADStackCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field269, budget)
            field269.append(field271^)
        var field273 = reader.count(budget)
        var field272 = List[Int]()
        for _ in range(field273):
            var field274 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            _grow(field272, budget)
            field272.append(field274)
        var field276 = reader.count(budget)
        var field275 = List[core.AlgebraicPolynomialEvaluation]()
        for _ in range(field276):
            var field277 = _read_node[core.AlgebraicPolynomialEvaluation, C, D, E](reader, budget, depth + 1)
            _grow(field275, budget)
            field275.append(field277^)
        var field279 = reader.count(budget)
        var field278 = List[core.AlgebraicComparisonCertificate]()
        for _ in range(field279):
            var field280 = _read_node[core.AlgebraicComparisonCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field278, budget)
            field278.append(field280^)
        return rebind_var[T](core.CADCellCertificate(field268^, field269^, field272^, field275^, field278^))
    elif T == core.CADCoveringCertificate:
        var field285 = _read_node[core.CADCertificate, C, D, E](reader, budget, depth + 1)
        var field286 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field288 = reader.count(budget)
        var field287 = List[Int]()
        for _ in range(field288):
            var field289 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            _grow(field287, budget)
            field287.append(field289)
        return rebind_var[T](core.CADCoveringCertificate(field285^, field286, field287^))
    elif T == core.CADProjectionCertificate:
        var field292 = reader.count(budget)
        var field291 = List[Int64]()
        for _ in range(field292):
            var field293 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
            _grow(field291, budget)
            field291.append(field293)
        var field294 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var field296 = reader.count(budget)
        var field295 = List[List[core.SparsePoly[core.QQ]]]()
        for _ in range(field296):
            var field298 = reader.count(budget)
            var field297 = List[core.SparsePoly[core.QQ]]()
            for _ in range(field298):
                var field299 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
                _grow(field297, budget)
                field297.append(field299^)
            _grow(field295, budget)
            field295.append(field297^)
        var field301 = reader.count(budget)
        var field300 = List[core.MultivariateFactorization[core.QQ]]()
        for _ in range(field301):
            var field302 = _read_node[core.MultivariateFactorization[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field300, budget)
            field300.append(field302^)
        var field304 = reader.count(budget)
        var field303 = List[core.ProjectionResultantCertificate]()
        for _ in range(field304):
            var field305 = _read_node[core.ProjectionResultantCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field303, budget)
            field303.append(field305^)
        var field307 = reader.count(budget)
        var field306 = List[core.CoprimalityCertificate[core.QQ]]()
        for _ in range(field307):
            var field308 = _read_node[core.CoprimalityCertificate[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field306, budget)
            field306.append(field308^)
        return rebind_var[T](core.CADProjectionCertificate(field291^, field294, field295^, field300^, field303^, field306^))
    elif T == core.CADConflict:
        var field315 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field316 = _read_node[core.AlgebraicPolynomialEvaluation, C, D, E](reader, budget, depth + 1)
        var field317 = _read_node[core.AlgebraicComparisonCertificate, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.CADConflict(field315, field316^, field317^))
    elif T == core.CADConflictInterval:
        var field318 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field319 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field320 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field321 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field322 = _read_node[core.CADConflict, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.CADConflictInterval(field318, field319, field320, field321, field322^))
    elif T == core.CylindricalCoveringCertificate:
        var field323 = _read_node[core.CADProjectionCertificate, C, D, E](reader, budget, depth + 1)
        var field325 = reader.count(budget)
        var field324 = List[core.CADCell]()
        for _ in range(field325):
            var field326 = _read_node[core.CADCell, C, D, E](reader, budget, depth + 1)
            _grow(field324, budget)
            field324.append(field326^)
        var field328 = reader.count(budget)
        var field327 = List[core.CADStackCertificate]()
        for _ in range(field328):
            var field329 = _read_node[core.CADStackCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field327, budget)
            field327.append(field329^)
        var field331 = reader.count(budget)
        var field330 = List[core.CADConflictInterval]()
        for _ in range(field331):
            var field332 = _read_node[core.CADConflictInterval, C, D, E](reader, budget, depth + 1)
            _grow(field330, budget)
            field330.append(field332^)
        var field333 = Optional[core.CADConflict]()
        if reader.number(1, budget):
            var field334 = _read_node[core.CADConflict, C, D, E](reader, budget, depth + 1)
            field333 = field334^
        var field335 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.CylindricalCoveringCertificate(field323^, field324^, field327^, field330^, field333^, field335))
    elif T == core.CoveringBound:
        var polynomial = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var root = _read_node[Int, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.CoveringBound(polynomial, root))
    elif T == core.CoveringInterval:
        var ends = reader.number(3, budget)
        var lower = Optional[core.CoveringBound]()
        var upper = Optional[core.CoveringBound]()
        if ends & 1:
            lower = _read_node[core.CoveringBound, C, D, E](reader, budget, depth + 1)
        if ends & 2:
            upper = _read_node[core.CoveringBound, C, D, E](reader, budget, depth + 1)
        var lower_closed = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var upper_closed = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var sample = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var constraint = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var child = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var count = reader.count(budget)
        var polynomials = List[Int]()
        for _ in range(count):
            var index = _read_node[Int, C, D, E](reader, budget, depth + 1)
            _grow(polynomials, budget)
            polynomials.append(index)
        return rebind_var[T](core.CoveringInterval(lower^, upper^, lower_closed, upper_closed, sample^, constraint, child, polynomials^))
    elif T == core.CoveringNode:
        var parent = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var interval = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var level = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var count = reader.count(budget)
        var intervals = List[core.CoveringInterval]()
        for _ in range(count):
            var item = _read_node[core.CoveringInterval, C, D, E](reader, budget, depth + 1)
            _grow(intervals, budget)
            intervals.append(item^)
        return rebind_var[T](core.CoveringNode(parent, interval, level, intervals^))
    elif T == core.CADCoveringsCertificate:
        var count = reader.count(budget)
        var variables = List[Int64]()
        for _ in range(count):
            var variable = _read_node[Int64, C, D, E](reader, budget, depth + 1)
            _grow(variables, budget)
            variables.append(variable)
        count = reader.count(budget)
        var polynomials = List[core.SparsePoly[core.QQ]]()
        for _ in range(count):
            var f = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(polynomials, budget)
            polynomials.append(f^)
        count = reader.count(budget)
        var input_factors = List[core.MultivariateFactorization[core.QQ]]()
        for _ in range(count):
            var proof = _read_node[core.MultivariateFactorization[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(input_factors, budget)
            input_factors.append(proof^)
        count = reader.count(budget)
        var projections = List[core.MultivariateFactorization[core.QQ]]()
        for _ in range(count):
            var proof = _read_node[core.MultivariateFactorization[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(projections, budget)
            projections.append(proof^)
        count = reader.count(budget)
        var nodes = List[core.CoveringNode]()
        for _ in range(count):
            var node = _read_node[core.CoveringNode, C, D, E](reader, budget, depth + 1)
            _grow(nodes, budget)
            nodes.append(node^)
        var root_conflict = _read_node[Int, C, D, E](reader, budget, depth + 1)
        count = reader.count(budget)
        var witness = List[core.RealAlgebraic]()
        for _ in range(count):
            var coordinate = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(witness, budget)
            witness.append(coordinate^)
        count = reader.count(budget)
        var evaluations = List[core.AlgebraicPolynomialEvaluation]()
        for _ in range(count):
            var evaluation = _read_node[core.AlgebraicPolynomialEvaluation, C, D, E](reader, budget, depth + 1)
            _grow(evaluations, budget)
            evaluations.append(evaluation^)
        count = reader.count(budget)
        var signs = List[core.AlgebraicComparisonCertificate]()
        for _ in range(count):
            var sign = _read_node[core.AlgebraicComparisonCertificate, C, D, E](reader, budget, depth + 1)
            _grow(signs, budget)
            signs.append(sign^)
        return rebind_var[T](core.CADCoveringsCertificate(variables^, polynomials^, input_factors^, projections^, nodes^, root_conflict, witness^, evaluations^, signs^))
    elif T == core.LazardEvaluationCertificate:
        var field340 = reader.count(budget)
        var field339 = List[Int]()
        for _ in range(field340):
            var field341 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            _grow(field339, budget)
            field339.append(field341)
        var field343 = reader.count(budget)
        var field342 = List[core.AlgebraicSpecializationCertificate]()
        for _ in range(field343):
            var field344 = _read_node[core.AlgebraicSpecializationCertificate, C, D, E](reader, budget, depth + 1)
            _grow(field342, budget)
            field342.append(field344^)
        return rebind_var[T](core.LazardEvaluationCertificate(field339^, field342^))
    elif T == core.DeterminantStep:
        var field347 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field349 = reader.count(budget)
        var field348 = List[List[core.SparsePoly[core.QQ]]]()
        for _ in range(field349):
            var field351 = reader.count(budget)
            var field350 = List[core.SparsePoly[core.QQ]]()
            for _ in range(field351):
                var field352 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
                _grow(field350, budget)
                field350.append(field352^)
            _grow(field348, budget)
            field348.append(field350^)
        return rebind_var[T](core.DeterminantStep(field347, field348^))
    elif T == core.ProjectionResultantCertificate:
        var field355 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
        var field356 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field358 = reader.count(budget)
        var field357 = List[core.DeterminantStep]()
        for _ in range(field358):
            var field359 = _read_node[core.DeterminantStep, C, D, E](reader, budget, depth + 1)
            _grow(field357, budget)
            field357.append(field359^)
        return rebind_var[T](core.ProjectionResultantCertificate(field355, field356^, field357^))
    elif T == core.NumericBox:
        var field361 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var field362 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var field363 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var field364 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.NumericBox(field361^, field362^, field363^, field364^))
    elif T == core.RealRootCell:
        var field365 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
        var field366 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field367 = _read_node[UInt8, C, D, E](reader, budget, depth + 1)
        var field369 = reader.count(budget)
        var field368 = List[core.EnclosureEvaluation[core.BallDomain]]()
        for _ in range(field369):
            var field370 = _read_node[core.EnclosureEvaluation[core.BallDomain], C, D, E](reader, budget, depth + 1)
            _grow(field368, budget)
            field368.append(field370^)
        return rebind_var[T](core.RealRootCell(field365^, field366, field367, field368^))
    elif T == core.RealRootResult:
        var field372 = _read_node[core.NumericOutcome, C, D, E](reader, budget, depth + 1)
        var field373 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var field374 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var field375 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var field377 = reader.count(budget)
        var field376 = List[core.RealRootCell]()
        for _ in range(field377):
            var field378 = _read_node[core.RealRootCell, C, D, E](reader, budget, depth + 1)
            _grow(field376, budget)
            field376.append(field378^)
        var field379 = Optional[core.SturmSequence]()
        if reader.number(1, budget):
            var field380 = _read_node[core.SturmSequence, C, D, E](reader, budget, depth + 1)
            field379 = field380^
        return rebind_var[T](core.RealRootResult(field372^, field373, field374, field375, field376^, field379^))
    elif T == core.RootInterval:
        var low = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var high = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.RootInterval(low^, high^))
    elif T == core.DescartesLeaf:
        var low = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var high = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var variations = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var resolved = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.DescartesLeaf(low^, high^, variations, resolved))
    elif T == core.DescartesCertificate:
        var low = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var high = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var leaf_count = reader.count(budget)
        var leaves = List[core.DescartesLeaf]()
        for _ in range(leaf_count):
            var leaf = _read_node[core.DescartesLeaf, C, D, E](reader, budget, depth + 1)
            _grow(leaves, budget)
            leaves.append(leaf^)
        var root_count = reader.count(budget)
        var exact_roots = List[core.QQ]()
        for _ in range(root_count):
            var root = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
            _grow(exact_roots, budget)
            exact_roots.append(root^)
        var bracket_count = reader.count(budget)
        var brackets = List[core.RootInterval]()
        for _ in range(bracket_count):
            var bracket = _read_node[core.RootInterval, C, D, E](reader, budget, depth + 1)
            _grow(brackets, budget)
            brackets.append(bracket^)
        return rebind_var[T](core.DescartesCertificate(low^, high^, leaves^, exact_roots^, brackets^))
    elif T == core.DescartesRootResult:
        var outcome = _read_node[core.NumericOutcome, C, D, E](reader, budget, depth + 1)
        var complete = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var accurate = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var isolated = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var squarefree = _read_node[core.DensePoly[core.ZZ], C, D, E](reader, budget, depth + 1)
        var cofactor = _read_node[core.DensePoly[core.ZZ], C, D, E](reader, budget, depth + 1)
        var bound_exponent = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var certificate = _read_node[core.DescartesCertificate, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.DescartesRootResult(outcome^, complete, accurate, isolated, squarefree^, cofactor^, bound_exponent, certificate^))
    elif T == core.AlgebraicDescartesCertificate:
        var squarefree = _read_node[core.DensePoly[core.ZZ], C, D, E](reader, budget, depth + 1)
        var cofactor = _read_node[core.DensePoly[core.ZZ], C, D, E](reader, budget, depth + 1)
        var bound_exponent = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var certificate = _read_node[core.DescartesCertificate, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.AlgebraicDescartesCertificate(squarefree^, cofactor^, bound_exponent, certificate^))
    elif T == core.ComplexBoundarySegment:
        var field382 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
        var field383 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
        var field384 = _read_node[core.EnclosureEvaluation[core.ComplexBallDomain], C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.ComplexBoundarySegment(field382^, field383^, field384^))
    elif T == core.ComplexRootRegion:
        var field385 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
        var field386 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field388 = reader.count(budget)
        var field387 = List[core.ComplexBoundarySegment]()
        for _ in range(field388):
            var field389 = _read_node[core.ComplexBoundarySegment, C, D, E](reader, budget, depth + 1)
            _grow(field387, budget)
            field387.append(field389^)
        return rebind_var[T](core.ComplexRootRegion(field385^, field386, field387^))
    elif T == core.ComplexRootResult:
        var field391 = _read_node[core.NumericOutcome, C, D, E](reader, budget, depth + 1)
        var field392 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var field393 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var field394 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var field396 = reader.count(budget)
        var field395 = List[core.ComplexRootRegion]()
        for _ in range(field396):
            var field397 = _read_node[core.ComplexRootRegion, C, D, E](reader, budget, depth + 1)
            _grow(field395, budget)
            field395.append(field397^)
        return rebind_var[T](core.ComplexRootResult(field391^, field392, field393, field394, field395^))
    elif T == core.RootMultiplicityCertificate:
        var field399 = _read_node[core.SquarefreeDecomposition[core.QQ], C, D, E](reader, budget, depth + 1)
        var block_count = reader.count(budget)
        var blocks = List[Int]()
        for _ in range(block_count):
            var block = _read_node[Int, C, D, E](reader, budget, depth + 1)
            _grow(blocks, budget)
            blocks.append(block)
        var field409 = reader.count(budget)
        var field408 = List[Int]()
        for _ in range(field409):
            var field410 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            _grow(field408, budget)
            field408.append(field410)
        return rebind_var[T](core.RootMultiplicityCertificate(field399^, blocks^, field408^))
    elif T == core.RootDiagnostics:
        var field414 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
        var field415 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
        var field416 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var field417 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
        var field418 = Optional[core.QQ]()
        if reader.number(1, budget):
            var field419 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
            field418 = field419^
        var field420 = Optional[core.QQ]()
        if reader.number(1, budget):
            var field421 = _read_node[core.QQ, C, D, E](reader, budget, depth + 1)
            field420 = field421^
        return rebind_var[T](core.RootDiagnostics(field414^, field415^, field416^, field417^, field418^, field420^))
    elif T == core.PolishedRootResult:
        var field422 = _read_node[apn.Complex, C, D, E](reader, budget, depth + 1)
        var field423 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field424 = Optional[core.ComplexRootRegion]()
        if reader.number(1, budget):
            var field425 = _read_node[core.ComplexRootRegion, C, D, E](reader, budget, depth + 1)
            field424 = field425^
        var field426 = _read_node[core.NumericOutcome, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.PolishedRootResult(field422^, field423, field424^, field426^))
    elif T == core.NumericDivisionStep:
        var field427 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
        var field429 = reader.count(budget)
        var field428 = List[core.NumericBox]()
        for _ in range(field429):
            var field430 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
            _grow(field428, budget)
            field428.append(field430^)
        return rebind_var[T](core.NumericDivisionStep(field427^, field428^))
    elif T == core.NumericDivisionResult[D]:
        var field432 = _read_node[core.NumericDensePoly[D], C, D, E](reader, budget, depth + 1)
        var field433 = _read_node[core.NumericDensePoly[D], C, D, E](reader, budget, depth + 1)
        var field435 = reader.count(budget)
        var field434 = List[core.NumericBox]()
        for _ in range(field435):
            var field436 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
            _grow(field434, budget)
            field434.append(field436^)
        var field438 = reader.count(budget)
        var field437 = List[core.NumericDivisionStep]()
        for _ in range(field438):
            var field439 = _read_node[core.NumericDivisionStep, C, D, E](reader, budget, depth + 1)
            _grow(field437, budget)
            field437.append(field439^)
        var field440 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.NumericDivisionResult[D](field432^, field433^, field434^, field437^, field440))
    elif T == core.SparseSquarefreeDecomposition[C]:
        var field443 = _read_node[C, C, D, E](reader, budget, depth + 1)
        var field445 = reader.count(budget)
        var field444 = List[Tuple[core.SparsePoly[C], Int]]()
        for _ in range(field445):
            var field447 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
            var field448 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            var field446 = (field447^, field448)
            _grow(field444, budget)
            field444.append(field446^)
        return rebind_var[T](core.SparseSquarefreeDecomposition[C](field443^, field444^))
    elif T == core.MultivariateFactorization[C]:
        var field450 = _read_node[C, C, D, E](reader, budget, depth + 1)
        var field452 = reader.count(budget)
        var field451 = List[Tuple[core.SparsePoly[C], Int]]()
        for _ in range(field452):
            var field454 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
            var field455 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            var field453 = (field454^, field455)
            _grow(field451, budget)
            field451.append(field453^)
        return rebind_var[T](core.MultivariateFactorization[C](field450^, field451^))
    elif T == exact._Data[C, E]:
        var field457 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field459 = reader.count(budget)
        var field458 = List[core.SparsePoly[C]]()
        for _ in range(field459):
            var field460 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
            _grow(field458, budget)
            field458.append(field460^)
        var field461 = _read_node[E, C, D, E](reader, budget, depth + 1)
        var field462 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field464 = reader.count(budget)
        var field463 = List[Optional[core.Factorization[C]]]()
        for _ in range(field464):
            var field465 = Optional[core.Factorization[C]]()
            if reader.number(1, budget):
                var field466 = _read_node[core.Factorization[C], C, D, E](reader, budget, depth + 1)
                field465 = field466^
            _grow(field463, budget)
            field463.append(field465^)
        return rebind_var[T](exact._Data[C, E](field457^, field458^, field461^, field462, field463^))
    elif T == exact._Interpolation[C]:
        var field470 = reader.count(budget)
        var field469 = List[C]()
        for _ in range(field470):
            var field471 = _read_node[C, C, D, E](reader, budget, depth + 1)
            _grow(field469, budget)
            field469.append(field471^)
        var field473 = reader.count(budget)
        var field472 = List[C]()
        for _ in range(field473):
            var field474 = _read_node[C, C, D, E](reader, budget, depth + 1)
            _grow(field472, budget)
            field472.append(field474^)
        var field476 = reader.count(budget)
        var field475 = List[List[C]]()
        for _ in range(field476):
            var field478 = reader.count(budget)
            var field477 = List[C]()
            for _ in range(field478):
                var field479 = _read_node[C, C, D, E](reader, budget, depth + 1)
                _grow(field477, budget)
                field477.append(field479^)
            _grow(field475, budget)
            field475.append(field477^)
        var field480 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        var field481 = _read_node[Bool, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](exact._Interpolation[C](field469^, field472^, field475^, field480, field481))
    elif T == roots._ExactData:
        var field487 = reader.count(budget)
        var field486 = List[core.RealAlgebraic]()
        for _ in range(field487):
            var field488 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field486, budget)
            field486.append(field488^)
        var field489 = _read_node[core.AlgebraicRootsCertificate, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](roots._ExactData(field486^, field489^))
    elif T == roots._CountData:
        var field491 = _read_node[core.DensePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field492 = _read_node[core.DescartesCountCertificate, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](roots._CountData(field491^, field492^))
    elif T == roots._RealCoverData[_CoreKind[C]]:
        var field493 = _read_node[core.DensePoly[_common._Ring[_CoreKind[C]]], C, D, E](reader, budget, depth + 1)
        var field494 = _read_node[core.NumericOptions, C, D, E](reader, budget, depth + 1)
        var field495 = _read_node[core.DescartesRootResult, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](roots._RealCoverData[_CoreKind[C]](field493^, field494^, field495^))
    elif T == roots._ComplexCoverData[_CoreKind[C]]:
        var field496 = _read_node[core.DensePoly[_common._Ring[_CoreKind[C]]], C, D, E](reader, budget, depth + 1)
        var field497 = _read_node[core.NumericOptions, C, D, E](reader, budget, depth + 1)
        var field498 = _read_node[core.ComplexRootResult, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](roots._ComplexCoverData[_CoreKind[C]](field496^, field497^, field498^))
    elif T == cad._DecompositionData:
        var field500 = reader.count(budget)
        var field499 = List[core.SparsePoly[core.QQ]]()
        for _ in range(field500):
            var field501 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field499, budget)
            field499.append(field501^)
        var pending = _read_final_cad[C, D, E](reader, False, budget, depth + 1)
        var field503 = Optional[ArcPointer[_cad_algebraic._Embedding]]()
        var scope = reader.number(3, budget)
        if scope & 1:
            var field505 = _read_node[_cad_algebraic._Embedding, C, D, E](reader, budget, depth + 1)
            _allocation[_cad_algebraic._Embedding](1, budget)
            var field504 = ArcPointer(field505^)
            field503 = field504^
        var fixed = List[Tuple[Int, algebraic.Real]]()
        if scope & 2:
            var count = reader.count(budget)
            if count == 0:
                raise _bad("empty fixed-coordinate CAD scope extension")
            for _ in range(count):
                var axis = _read_node[Int, C, D, E](reader, budget, depth + 1)
                var value = _read_node[algebraic.Real, C, D, E](reader, budget, depth + 1)
                _grow(fixed, budget)
                fixed.append((axis, value^))
        var field502 = _accept_final_cad(pending^, field499, List[UInt8](), False, field503, fixed, budget)
        return rebind_var[T](cad._DecompositionData(field499^, field502^, field503^, fixed^))
    elif T == cad._SolutionData:
        var field508 = reader.count(budget)
        var field507 = List[core.SparsePoly[core.QQ]]()
        for _ in range(field508):
            var field509 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field507, budget)
            field507.append(field509^)
        var field511 = reader.count(budget)
        var field510 = List[UInt8]()
        for _ in range(field511):
            var field512 = _read_node[UInt8, C, D, E](reader, budget, depth + 1)
            _grow(field510, budget)
            field510.append(field512)
        var field513 = _read_node[core.CADCoveringsCertificate, C, D, E](reader, budget, depth + 1)
        var field514 = Optional[ArcPointer[_cad_algebraic._Embedding]]()
        var scope = reader.number(3, budget)
        if scope & 1:
            var field516 = _read_node[_cad_algebraic._Embedding, C, D, E](reader, budget, depth + 1)
            _allocation[_cad_algebraic._Embedding](1, budget)
            var field515 = ArcPointer(field516^)
            field514 = field515^
        var fixed = List[Tuple[Int, algebraic.Real]]()
        if scope & 2:
            var count = reader.count(budget)
            if count == 0:
                raise _bad("empty fixed-coordinate CAD scope extension")
            for _ in range(count):
                var axis = _read_node[Int, C, D, E](reader, budget, depth + 1)
                var value = _read_node[algebraic.Real, C, D, E](reader, budget, depth + 1)
                _grow(fixed, budget)
                fixed.append((axis, value^))
        return rebind_var[T](cad._SolutionData(field507^, field510^, field513^, field514^, fixed^))
    elif T == cad._ProjectionData:
        var field520 = reader.count(budget)
        var field519 = List[core.SparsePoly[core.QQ]]()
        for _ in range(field520):
            var field521 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field519, budget)
            field519.append(field521^)
        var field523 = reader.count(budget)
        var field522 = List[Int64]()
        for _ in range(field523):
            var field524 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
            _grow(field522, budget)
            field522.append(field524)
        var field525 = _read_node[core.CADProjectionCertificate, C, D, E](reader, budget, depth + 1)
        var field526 = Optional[ArcPointer[_cad_algebraic._Embedding]]()
        if reader.number(1, budget):
            var field528 = _read_node[_cad_algebraic._Embedding, C, D, E](reader, budget, depth + 1)
            _allocation[_cad_algebraic._Embedding](1, budget)
            var field527 = ArcPointer(field528^)
            field526 = field527^
        return rebind_var[T](cad._ProjectionData(field519^, field522^, field525^, field526^))
    elif T == cad._CellAtData:
        var field532 = reader.count(budget)
        var field531 = List[core.SparsePoly[core.QQ]]()
        for _ in range(field532):
            var field533 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field531, budget)
            field531.append(field533^)
        var field535 = reader.count(budget)
        var field534 = List[Int64]()
        for _ in range(field535):
            var field536 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
            _grow(field534, budget)
            field534.append(field536)
        var field538 = reader.count(budget)
        var field537 = List[core.RealAlgebraic]()
        for _ in range(field538):
            var field539 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            _grow(field537, budget)
            field537.append(field539^)
        var field540 = _read_node[core.CADCellCertificate, C, D, E](reader, budget, depth + 1)
        var field541 = Optional[ArcPointer[_cad_algebraic._Embedding]]()
        if reader.number(1, budget):
            var field543 = _read_node[_cad_algebraic._Embedding, C, D, E](reader, budget, depth + 1)
            _allocation[_cad_algebraic._Embedding](1, budget)
            var field542 = ArcPointer(field543^)
            field541 = field542^
        return rebind_var[T](cad._CellAtData(field531^, field534^, field537^, field540^, field541^))
    elif T == cad._LazardData:
        var field547 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field549 = reader.count(budget)
        var field548 = List[Tuple[Int64, core.RealAlgebraic]]()
        for _ in range(field549):
            var field551 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
            var field552 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            var field550 = (field551, field552^)
            _grow(field548, budget)
            field548.append(field550^)
        var field553 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
        var field554 = _read_node[core.LazardEvaluationCertificate, C, D, E](reader, budget, depth + 1)
        var field555 = Optional[ArcPointer[_cad_algebraic._Embedding]]()
        if reader.number(1, budget):
            var field557 = _read_node[_cad_algebraic._Embedding, C, D, E](reader, budget, depth + 1)
            _allocation[_cad_algebraic._Embedding](1, budget)
            var field556 = ArcPointer(field557^)
            field555 = field556^
        return rebind_var[T](cad._LazardData(field547^, field548^, field553, field554^, field555^))
    elif T == cad._CoveringData:
        var field560 = reader.count(budget)
        var field559 = List[core.SparsePoly[core.QQ]]()
        for _ in range(field560):
            var field561 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
            _grow(field559, budget)
            field559.append(field561^)
        var field563 = reader.count(budget)
        var field562 = List[UInt8]()
        for _ in range(field563):
            var field564 = _read_node[UInt8, C, D, E](reader, budget, depth + 1)
            _grow(field562, budget)
            field562.append(field564)
        var pending = _read_final_cad[C, D, E](reader, True, budget, depth + 1)
        var field566 = Optional[ArcPointer[_cad_algebraic._Embedding]]()
        var scope = reader.number(3, budget)
        if scope & 1:
            var field568 = _read_node[_cad_algebraic._Embedding, C, D, E](reader, budget, depth + 1)
            _allocation[_cad_algebraic._Embedding](1, budget)
            var field567 = ArcPointer(field568^)
            field566 = field567^
        var fixed = List[Tuple[Int, algebraic.Real]]()
        if scope & 2:
            var count = reader.count(budget)
            if count == 0:
                raise _bad("empty fixed-coordinate CAD scope extension")
            for _ in range(count):
                var axis = _read_node[Int, C, D, E](reader, budget, depth + 1)
                var value = _read_node[algebraic.Real, C, D, E](reader, budget, depth + 1)
                _grow(fixed, budget)
                fixed.append((axis, value^))
        var field565 = _accept_final_cad(pending^, field559, field562, True, field566, fixed, budget)
        return rebind_var[T](cad._CoveringData(field559^, field562^, field565^, field566^, fixed^))
    elif T == _cad_algebraic._Embedding:
        var field572 = reader.count(budget)
        var field571 = List[core.SparsePoly[_algebraic_value.Real]]()
        for _ in range(field572):
            var field573 = _read_node[core.SparsePoly[_algebraic_value.Real], C, D, E](reader, budget, depth + 1)
            _grow(field571, budget)
            field571.append(field573^)
        var field575 = reader.count(budget)
        var field574 = List[_algebraic_value.Real]()
        for _ in range(field575):
            var field576 = _read_node[_algebraic_value.Real, C, D, E](reader, budget, depth + 1)
            _grow(field574, budget)
            field574.append(field576^)
        var field577 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](_cad_algebraic._Embedding(field571^, field574^, field577))
    elif T == _complex_roots._Data:
        var field580 = _read_node[core.DensePoly[_algebraic_value.Complex], C, D, E](reader, budget, depth + 1)
        var field581 = _read_node[_complex_roots.ComplexRootsCertificate, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](_complex_roots._Data(field580^, field581^))
    elif T == _complex_roots.ComplexRootsCertificate:
        var field583 = reader.count(budget)
        var field582 = List[_algebraic_value.Complex]()
        for _ in range(field583):
            var field584 = _read_node[_algebraic_value.Complex, C, D, E](reader, budget, depth + 1)
            _grow(field582, budget)
            field582.append(field584^)
        var field586 = reader.count(budget)
        var field585 = List[Int]()
        for _ in range(field586):
            var field587 = _read_node[Int, C, D, E](reader, budget, depth + 1)
            _grow(field585, budget)
            field585.append(field587)
        return rebind_var[T](_complex_roots.ComplexRootsCertificate(field582^, field585^))
    elif T == _algebraic_numeric._Witness:
        var field590 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        var field591 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](_algebraic_numeric._Witness(field590^, field591^))
    elif T == _rational_field.RationalFunction[F]:
        var field592 = _read_node[core.SparsePoly[F], C, D, E](reader, budget, depth + 1)
        var field593 = _read_node[core.SparsePoly[F], C, D, E](reader, budget, depth + 1)
        return rebind_var[T](_rational_field.RationalFunction[F](field592^, field593^))
    elif T == _rational_field.Cancellation[F]:
        var field594 = _read_node[core.SparsePoly[F], C, D, E](reader, budget, depth + 1)
        var field596 = _read_node[core.SparsePoly[F], C, D, E](reader, budget, depth + 1)
        var field597 = _read_node[core.SparsePoly[F], C, D, E](reader, budget, depth + 1)
        var field595 = (field596^, field597^)
        return rebind_var[T](_rational_field.Cancellation[F](field594^, field595^))
    elif T == _rational_field.PartialFractionTerm[F]:
        var field598 = _read_node[core.DensePoly[F], C, D, E](reader, budget, depth + 1)
        var field599 = _read_node[core.DensePoly[F], C, D, E](reader, budget, depth + 1)
        var field600 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](_rational_field.PartialFractionTerm[F](field598^, field599^, field600))
    elif T == _rational_field.LaurentExpansion[F]:
        var field601 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
        var field602 = _read_node[F, C, D, E](reader, budget, depth + 1)
        var field603 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field605 = reader.count(budget)
        var field604 = List[F]()
        for _ in range(field605):
            var field606 = _read_node[F, C, D, E](reader, budget, depth + 1)
            _grow(field604, budget)
            field604.append(field606^)
        return rebind_var[T](_rational_field.LaurentExpansion[F](field601, field602^, field603, field604^))
    elif T == _rational_certificates._Irreducibility:
        var field608 = _read_node[UInt64, C, D, E](reader, budget, depth + 1)
        var field609 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](_rational_certificates._Irreducibility(field608, field609))
    elif T == _rational_certificates._Factors[F]:
        var field610 = _read_node[core.Factorization[F], C, D, E](reader, budget, depth + 1)
        var field612 = reader.count(budget)
        var field611 = List[_rational_certificates._Irreducibility]()
        for _ in range(field612):
            var field613 = _read_node[_rational_certificates._Irreducibility, C, D, E](reader, budget, depth + 1)
            _grow(field611, budget)
            field611.append(field613^)
        return rebind_var[T](_rational_certificates._Factors[F](field610^, field611^))
    elif T == _determinant.Step[C]:
        var field615 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field617 = reader.count(budget)
        var field616 = List[List[core.SparsePoly[C]]]()
        for _ in range(field617):
            var field619 = reader.count(budget)
            var field618 = List[core.SparsePoly[C]]()
            for _ in range(field619):
                var field620 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
                _grow(field618, budget)
                field618.append(field620^)
            _grow(field616, budget)
            field616.append(field618^)
        return rebind_var[T](_determinant.Step[C](field615, field616^))
    elif T == _determinant.Certificate[C]:
        var field623 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
        var field624 = _read_node[core.SparsePoly[C], C, D, E](reader, budget, depth + 1)
        var field626 = reader.count(budget)
        var field625 = List[_determinant.Step[C]]()
        for _ in range(field626):
            var field627 = _read_node[_determinant.Step[C], C, D, E](reader, budget, depth + 1)
            _grow(field625, budget)
            field625.append(field627^)
        return rebind_var[T](_determinant.Certificate[C](field623, field624^, field625^))
    elif T == algebraic._SpecializationData:
        var field629 = _read_node[core.SparsePoly[core.QQ], C, D, E](reader, budget, depth + 1)
        var field631 = reader.count(budget)
        var field630 = List[Tuple[Int64, core.RealAlgebraic]]()
        for _ in range(field631):
            var field633 = _read_node[Int64, C, D, E](reader, budget, depth + 1)
            var field634 = _read_node[core.RealAlgebraic, C, D, E](reader, budget, depth + 1)
            var field632 = (field633, field634^)
            _grow(field630, budget)
            field630.append(field632^)
        var field635 = _read_node[core.AlgebraicSpecializationCertificate, C, D, E](reader, budget, depth + 1)
        return rebind_var[T](algebraic._SpecializationData(field629^, field630^, field635^))
    elif T == _algebraic_numeric._Polynomial[core.ComplexBallDomain, False]:
        var field637 = _read_node[core.NumericDensePoly[core.ComplexBallDomain], C, D, E](reader, budget, depth + 1)
        var field639 = reader.count(budget)
        var field638 = List[_algebraic_numeric._Witness]()
        for _ in range(field639):
            var field640 = _read_node[_algebraic_numeric._Witness, C, D, E](reader, budget, depth + 1)
            _grow(field638, budget)
            field638.append(field640^)
        return rebind_var[T](_algebraic_numeric._Polynomial[core.ComplexBallDomain, False](field637^, field638^))
    elif T == _algebraic_numeric._Polynomial[D, False]:
        var value = _read_node[core.NumericDensePoly[D], C, D, E](reader, budget, depth + 1)
        var witnesses = List[_algebraic_numeric._Witness]()
        for _ in range(reader.count(budget)):
            var witness = _read_node[_algebraic_numeric._Witness, C, D, E](reader, budget, depth + 1)
            _grow(witnesses, budget)
            witnesses.append(witness^)
        return rebind_var[T](_algebraic_numeric._Polynomial[D, False](value^, witnesses^))
    elif T == _algebraic_numeric._Polynomial[D, True]:
        var value = _read_node[core.NumericSparsePoly[D], C, D, E](reader, budget, depth + 1)
        var witnesses = List[_algebraic_numeric._Witness]()
        for _ in range(reader.count(budget)):
            var witness = _read_node[_algebraic_numeric._Witness, C, D, E](reader, budget, depth + 1)
            _grow(witnesses, budget)
            witnesses.append(witness^)
        return rebind_var[T](_algebraic_numeric._Polynomial[D, True](value^, witnesses^))
    elif T == core.EnclosureEvaluation[D]:
        var field642 = _read_node[Int, C, D, E](reader, budget, depth + 1)
        var field644 = reader.count(budget)
        var field643 = List[D.Scalar]()
        for _ in range(field644):
            var field645 = _read_node[D.Scalar, C, D, E](reader, budget, depth + 1)
            _grow(field643, budget)
            field643.append(field645^)
        var field647 = reader.count(budget)
        var field646 = List[core.NumericBox]()
        for _ in range(field647):
            var field648 = _read_node[core.NumericBox, C, D, E](reader, budget, depth + 1)
            _grow(field646, budget)
            field646.append(field648^)
        return rebind_var[T](core.EnclosureEvaluation[D](field642, field643^, field646^))
    elif T == core.AdaptiveEvaluation[D]:
        var field651 = _read_node[core.NumericOutcome, C, D, E](reader, budget, depth + 1)
        var field652 = _read_node[core.EnclosureEvaluation[D], C, D, E](reader, budget, depth + 1)
        return rebind_var[T](core.AdaptiveEvaluation[D](field651^, field652^))
    else:
        comptime assert False, "unsupported certificate node"
