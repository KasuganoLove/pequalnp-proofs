"""Independent polynomial-only verification of the saved row-zero certificate.

This does not invoke a Groebner algorithm.  It checks both the connection to
the actual cubic chart equations and the explicit contradiction identity.
"""
import itertools
import json
from pathlib import Path
import resource
import time

resource.setrlimit(resource.RLIMIT_CPU, (20, 21))
resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
import sympy as s

started = time.monotonic()
d = json.loads(Path(__file__).with_name('rowzero-rational-certificate.json').read_text())
a, b, c, r = s.symbols('a b c r')
x, y, z = s.symbols('x y z')
E = list(map(s.sympify, d['equations']))
H = list(map(s.sympify, d['integer_multipliers']))
G = s.sympify(d['integer_root_relation_multiplier'])
constant = s.Integer(d['constant'])
assert len(E) == len(H) == 10
assert constant != 0
assert s.expand(sum(h*e for h, e in zip(H, E)) + G*(r*r+2) - constant) == 0

p = s.Matrix([x, y, z])
q = s.Matrix([[0, a, b], [-a, 0, c], [-b, -c, 0]])*p
C = s.diag(*(p[k]+q[k] for k in range(3)))
for k, (i, j) in enumerate([(1, 2), (0, 2), (0, 1)]):
    C[i, j] = C[j, i] = r*(p[k]-q[k])/2
permanent = s.expand(sum(s.prod(C[i, perm[i]] for i in range(3))
                         for perm in itertools.permutations(range(3))))
actual = s.Poly(permanent, x, y, z).coeffs()
assert len(actual) == len(E)
for actual_equation, reduced_equation in zip(actual, E):
    _, remainder = s.div(s.expand(actual_equation-reduced_equation), r*r+2, r)
    assert s.expand(remainder) == 0

print(json.dumps({
    'nonzero_constant': int(constant),
    'exact_contradiction_identity_verified': True,
    'chart_equations_match_permanent_modulo_root_relation': True,
    'groebner_invoked': False,
    'seconds': time.monotonic()-started,
    'lean_status': 'not compiled or checked in Lean'
}, indent=2))
