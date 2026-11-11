"""Adapt Lean's JSON protocol to SumOfSquares.py and return rational squares."""

import json
import sys

import numpy as np
import sympy as sp
from SumOfSquares import SOSProblem


class NoCertificate(Exception):
    pass


def polynomial(tree, variables):
    """Translate the arithmetic tree to a SymPy polynomial."""
    budget = [2000]

    def visit(t):
        budget[0] -= 1
        if budget[0] < 0 or not isinstance(t, list) or not t:
            raise ValueError("invalid or oversized expression")
        op, *args = t
        if op == "num" and len(args) == 1 and type(args[0]) is int:
            return sp.Integer(args[0])
        if op == "var" and len(args) == 1 and type(args[0]) is int:
            if not 0 <= args[0] < len(variables):
                raise ValueError("variable index out of range")
            return variables[args[0]]
        if op == "neg" and len(args) == 1:
            return -visit(args[0])
        if op == "pow" and len(args) == 2 and type(args[1]) is int:
            if not 0 <= args[1] <= 2:
                raise ValueError("classroom adapter supports powers 0, 1, and 2")
            result = visit(args[0]) ** args[1]
        elif op in ("add", "sub", "mul", "div") and len(args) == 2:
            p, q = map(visit, args)
            if op == "add":
                result = p + q
            elif op == "sub":
                result = p - q
            elif op == "mul":
                result = p * q
            else:
                if q.free_symbols or q == 0:
                    raise ValueError("division requires a nonzero constant")
                result = p / q
        else:
            raise ValueError("unsupported expression")
        result = sp.expand(result)
        if result.free_symbols and sp.Poly(result, *variables).total_degree() > 2:
            raise ValueError("classroom adapter supports degree at most two")
        return result

    return visit(tree)


def rational_squares(constraint, p):
    """Recover exact weighted squares from the solver's numerical Gram matrix."""
    basis = sp.Matrix(constraint.b_sym)
    size = len(basis)
    q = sp.Matrix(np.asarray(constraint.Qval).reshape(size, size)).applyfunc(
        lambda value: sp.Rational(float(value)).limit_denominator(1_000_000)
    )
    # A nonsingular principal submatrix also handles certificates of deficient rank.
    _, pivots = q.rref()
    a = q.extract(pivots, pivots)
    lower, diagonal = a.LDLdecomposition(hermitian=False)
    forms = lower.T * a.inv() * q.extract(pivots, range(size)) * basis
    weights = list(diagonal.diagonal())
    if any(w <= 0 for w in weights) or sp.expand(sum(
        w * f**2 for w, f in zip(weights, forms)
    ) - p) != 0:
        raise NoCertificate("could not recover an exact rational certificate")
    return zip(weights, forms)


def find_sos(problem):
    n = problem["variables"]
    if type(n) is not int or not 0 <= n <= 8:
        raise ValueError("classroom adapter supports at most eight variables")
    variables = sp.symbols(f"x0:{n}")
    p = polynomial(problem["expression"], variables)
    if not p.free_symbols:
        if p < 0:
            raise NoCertificate("negative constant")
        squares = [(p, sp.Integer(1))] if p else []
    else:
        if sp.Poly(p, *variables).total_degree() != 2:
            raise NoCertificate("no SOS certificate for a nonconstant linear polynomial")
        problem = SOSProblem()
        constraint = problem.add_sos_constraint(p, list(variables))
        try:
            problem.solve(solver="cvxopt")
            squares = rational_squares(constraint, p)
        except Exception as error:
            raise NoCertificate(f"SOS search or rational reconstruction failed: {error}") from error

    def pair(q):
        return [int(q.p), int(q.q)]

    return [{"weight": pair(w), "form": [pair(f.subs(dict.fromkeys(variables, 0)))]
             + [pair(sp.diff(f, x)) for x in variables]} for w, f in squares]


def main():
    try:
        text = sys.stdin.read(1_000_001)
        if len(text) > 1_000_000:
            raise ValueError("input too large")
        result = find_sos(json.loads(text))
    except NoCertificate as error:
        print(error, file=sys.stderr)
        return 2
    except (ValueError, TypeError, KeyError, RecursionError) as error:
        print(f"invalid SOS problem: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
