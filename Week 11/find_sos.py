"""Use SumOfSquares.py to find rational SOS candidates for Lean to verify."""

import json
import sys

try:
    import numpy as np
    import sympy as sp
    from SumOfSquares import SOSProblem
except ModuleNotFoundError as error:
    sys.exit(
        f"Missing SOS Python dependency: {error.name}.\n"
        "From the LeanClass repository root, run:\n"
        "  bash 'Week 11/setup_sos.sh'"
    )


class NoCertificate(Exception):
    pass


def polynomial(tree, variables):
    """Translate the arithmetic tree to a SymPy expression."""
    match tree:
        case ["num", n] if type(n) is int:
            return sp.Integer(n)
        case ["var", i] if type(i) is int and 0 <= i < len(variables):
            return variables[i]
        case ["neg", p]:
            return -polynomial(p, variables)
        case ["pow", p, n] if type(n) is int and n >= 0:
            return polynomial(p, variables) ** n
        case ["add", p, q]:
            return polynomial(p, variables) + polynomial(q, variables)
        case ["sub", p, q]:
            return polynomial(p, variables) - polynomial(q, variables)
        case ["mul", p, q]:
            return polynomial(p, variables) * polynomial(q, variables)
        case ["div", p, q]:
            denominator = sp.expand(polynomial(q, variables))
            if denominator.free_symbols or denominator == 0:
                raise ValueError("division requires a nonzero constant")
            return polynomial(p, variables) / denominator
        case _:
            raise ValueError("unsupported expression")


def rational_squares(constraint, p, variables):
    """Complete squares in the rationalized Gram matrix."""
    basis = sp.Matrix(constraint.b_sym)
    # Small denominators avoid fitting the solver's numerical noise.
    gram = sp.Matrix(np.asarray(constraint.Qval).reshape(len(basis), len(basis))).applyfunc(
        lambda value: sp.Rational(float(value)).limit_denominator(1000)
    )
    # Restore the polynomial's exact coefficients after rounding the matrix.
    residual = sp.Poly(p - (basis.T * gram * basis)[0], *variables)
    for i in range(len(basis)):
        for j in range(i, len(basis)):
            monomial = basis[i] * basis[j]
            correction = residual.coeff_monomial(monomial)
            gram[i, j] += correction if i == j else correction / 2
            if i != j:
                gram[j, i] += correction / 2
            residual -= sp.Poly(correction * monomial, *variables)
    squares = []
    for i in range(len(basis)):
        weight = gram[i, i]
        column = gram[:, i]
        if weight > 0:
            coefficients = column / weight
            squares.append((weight, coefficients.dot(basis)))
            gram -= weight * coefficients * coefficients.T
        elif not column.is_zero_matrix:
            raise ValueError("rationalized Gram matrix failed the positive semidefinite check")
    return squares


def lean_term(expr):
    """Print polynomial arithmetic with exact coefficients in Lean syntax."""
    if expr.is_Rational:
        return str(expr.p) if expr.q == 1 else f"({expr.p} / {expr.q})"
    if expr.is_Symbol:
        return str(expr)
    if expr.is_Add or expr.is_Mul:
        operator = " + " if expr.is_Add else " * "
        return "(" + operator.join(lean_term(arg) for arg in expr.args) + ")"
    if expr.is_Pow:
        base, exponent = expr.args
        return f"({lean_term(base)} ^ {exponent})"
    raise ValueError(f"unsupported polynomial term: {expr}")


def find_sos(problem):
    names = problem["variables"]
    legacy = type(names) is int
    if legacy:
        if names < 0:
            raise ValueError("variable count must be nonnegative")
        names = [f"x{i}" for i in range(names)]
    if not isinstance(names, list) or any(not isinstance(name, str) or not name for name in names):
        raise ValueError("variables must be a list of names")
    if len(set(names)) != len(names):
        raise ValueError("variable names must be distinct")
    variables = tuple(sp.Symbol(name) for name in names)
    p = sp.expand(polynomial(problem["expression"], variables))
    if not p.free_symbols:
        if p < 0:
            raise NoCertificate("negative constant")
        squares = [(p, sp.Integer(1))] if p else []
    else:
        try:
            sos = SOSProblem()
            constraint = sos.add_sos_constraint(p, list(variables))
            sos.solve(solver="cvxopt")
            squares = rational_squares(constraint, p, variables)
        except Exception as error:
            raise NoCertificate(f"SOS search or rational reconstruction failed: {error}") from error

    if legacy:
        return affine_certificate(squares, variables)
    entries = [f"({lean_term(weight)}, {lean_term(form)})" for weight, form in squares]
    return "[" + ", ".join(entries) + "]"


def affine_certificate(squares, variables):
    """Keep the original Week 10 worksheets' coefficient protocol working."""
    def pair(q):
        return [int(q.p), int(q.q)]

    certificate = []
    origin = dict.fromkeys(variables, 0)
    for weight, form in squares:
        if form.free_symbols and sp.Poly(form, *variables).total_degree() > 1:
            raise ValueError("the Week 10 coefficient protocol requires affine squares")
        coefficients = [form.subs(origin)] + [sp.diff(form, x) for x in variables]
        certificate.append({"weight": pair(weight), "form": [pair(c) for c in coefficients]})
    return certificate


def main():
    try:
        result = find_sos(json.load(sys.stdin))
    except NoCertificate as error:
        print(error, file=sys.stderr)
        return 2
    except (ValueError, TypeError, KeyError, RecursionError) as error:
        print(f"invalid SOS problem: {error}", file=sys.stderr)
        return 1
    print(result if isinstance(result, str) else json.dumps(result, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
