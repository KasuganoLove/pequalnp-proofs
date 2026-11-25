"""Bounded exact search in a restricted row-zero symmetric 4x4 family.

This is not a Lean proof and does not assume that every task candidate has
zero row sums.  Run one chart per invocation to make the resource bound clear.
"""
import itertools
import json
import resource
import sys
import time

resource.setrlimit(resource.RLIMIT_CPU, (25, 26))
resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))

import sympy as s

started = time.monotonic()
chart = int(sys.argv[1]) if len(sys.argv) > 1 else 0
assert 0 <= chart < 8
a, b, c = params = s.symbols('a b c')
x, y, z = variables = s.symbols('x y z')
r = s.sqrt(-2)
H = s.Matrix([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]])
p = s.Matrix(variables)
q = s.Matrix([[0, a, b], [-a, 0, c], [-b, -c, 0]]) * p
C = s.diag(*(p[k] + q[k] for k in range(3)))
for k, (i, j) in enumerate([(1, 2), (0, 2), (0, 1)]):
    C[i, j] = C[j, i] = (-1 if chart & (1 << k) else 1) * r * (p[k] - q[k]) / 2
T = H * C * H.T
assert all(s.expand(sum(T[i, j] for j in range(4))) == 0 for i in range(4))
assert s.expand(sum(T[i, j]**2 for i in range(4) for j in range(4))) == 0

# For a row- and column-zero matrix the cubic Taylor coefficient at J is
# (2/3) sum(T_ij^3).  Its identity is checked independently in the assessment.
K = s.expand(s.Rational(2, 3) * sum(T[i, j]**3 for i in range(4) for j in range(4)))
P = s.expand(sum(s.prod(T[i, perm[i]] for i in range(4))
                 for perm in itertools.permutations(range(4))))
equations = s.Poly(K, *variables).coeffs() + s.Poly(P, *variables).coeffs()
equations = [s.Poly(e, *params, extension=r).monic().as_expr()
             for e in equations if e != 0]
equations = list(dict.fromkeys(equations))
print(json.dumps({'chart': chart, 'equations': len(equations),
                  'generation_seconds': time.monotonic() - started}), flush=True)
gb = s.groebner(equations, *params, extension=r, order='grevlex')
out = {'chart': chart, 'equations': len(equations),
       'basis': [str(e) for e in gb.polys],
       'unit_ideal': len(gb.polys) == 1 and gb.polys[0].as_expr() == 1,
       'seconds': time.monotonic() - started,
       'scope': 'restricted symmetric row-zero family; not the full task'}
print(json.dumps(out, indent=2), flush=True)
