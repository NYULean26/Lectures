"""Exercise the JSON protocol and check returned certificates exactly."""

from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import subprocess
import sys
import unittest


def num(n):
    return ["num", n]


def var(i):
    return ["var", i]


class SOSProtocolTests(unittest.TestCase):
    def search(self, n, expression):
        return subprocess.run(
            [sys.executable, str(Path(__file__).with_name("find_sos.py"))],
            input=json.dumps({"variables": n, "expression": expression}),
            capture_output=True, text=True, timeout=15,
        )

    def check_certificate(self, n, expression, expected):
        out = self.search(n, expression)
        self.assertEqual(out.returncode, 0, out.stderr)
        certificate = json.loads(out.stdout)
        for point in product(range(-2, 3), repeat=n):
            total = Fraction(0)
            for term in certificate:
                weight = Fraction(*term["weight"])
                self.assertGreaterEqual(weight, 0)
                self.assertEqual(len(term["form"]), n + 1)
                coefficients = [Fraction(*q) for q in term["form"]]
                value = coefficients[0] + sum(c*x for c, x in zip(coefficients[1:], point))
                total += weight * value**2
            self.assertEqual(total, expected(*point))

    def test_zero_and_constant(self):
        self.check_certificate(0, num(0), lambda: 0)
        self.check_certificate(0, num(7), lambda: 7)

    def test_single_square_and_unused_variable(self):
        self.check_certificate(2, ["pow", var(0), 2], lambda x, y: x*x)

    def test_singular_quadratic(self):
        self.check_certificate(2, ["pow", ["sub", var(0), var(1)], 2],
                               lambda x, y: (x-y)**2)

    def test_affine_rational_square(self):
        form = ["add", ["sub", var(0), ["mul", num(2), var(1)]], num(3)]
        self.check_certificate(2, ["div", ["pow", form, 2], num(3)],
                               lambda x, y: Fraction((x-2*y+3)**2, 3))

    def test_several_squares(self):
        expression = ["add", ["pow", ["add", var(0), var(1)], 2],
                      ["add", ["pow", ["sub", var(0), var(1)], 2], num(1)]]
        self.check_certificate(2, expression, lambda x, y: 2*x*x + 2*y*y + 1)

    def test_no_certificate(self):
        for expression in [num(-1), var(0), ["neg", ["pow", var(0), 2]],
                           ["sub", ["pow", var(0), 2], num(1)]]:
            out = self.search(1, expression)
            self.assertEqual(out.returncode, 2, out.stderr)
            self.assertEqual(out.stdout, "")

    def test_unsupported_input(self):
        for expression in [["pow", var(0), 4], ["div", num(1), var(0)],
                           ["div", num(1), num(0)], var(2), ["num", "7"],
                           ["num", True], ["unknown", num(1)]]:
            out = self.search(1, expression)
            self.assertEqual(out.returncode, 1, out.stderr)
            self.assertEqual(out.stdout, "")


if __name__ == "__main__":
    unittest.main()
