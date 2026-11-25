"""Extract and exactly verify a small Nullstellensatz certificate for one
row-zero isotropic graph chart.  Sign-parity charts are conjugate under r -> -r.
This remains a scoped algebra computation, not a Lean proof of L-gct-232.
"""
import itertools
import json
from pathlib import Path
import resource
import time

resource.setrlimit(resource.RLIMIT_CPU, (30, 31))
resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
import sympy as s
from sympy.polys.matrices import DomainMatrix

started = time.monotonic()
a, b, c = params = s.symbols('a b c')
x, y, z = variables = s.symbols('x y z')
r = s.sqrt(-2)
field = s.QQ.algebraic_field(r)
p = s.Matrix(variables)
q = s.Matrix([[0, a, b], [-a, 0, c], [-b, -c, 0]]) * p
D = [p[k]+q[k] for k in range(3)]
O = [r*(p[k]-q[k])/2 for k in range(3)]
K = s.expand(s.prod(D) + sum(D[k]*O[k]**2 for k in range(3)) + 2*s.prod(O))
polynomial = s.Poly(K, *variables)
equations = polynomial.coeffs()

for degree in range(4):
    monomials = [a**i*b**j*c**k for i, j, k in itertools.product(range(degree+1), repeat=3)
                 if i+j+k <= degree]
    columns = [s.Poly(m*e, *params, extension=r) for e in equations for m in monomials]
    powers = sorted(set(itertools.chain.from_iterable(P.monoms() for P in columns)) | {(0, 0, 0)})
    rows = [[P.coeff_monomial(mon) for P in columns] + [int(mon == (0, 0, 0))] for mon in powers]
    matrix = DomainMatrix.from_list_sympy(len(rows), len(rows[0]), rows).convert_to(field)
    reduced, pivots = matrix.rref()
    if len(columns) in pivots:
        continue
    result = reduced.to_Matrix()
    weights = [s.S.Zero] * len(columns)
    for row, col in enumerate(pivots):
        weights[col] = result[row, -1]
    multipliers = [s.expand(sum(weights[i*len(monomials)+j]*m for j, m in enumerate(monomials)))
                   for i in range(len(equations))]
    residual = s.Poly(sum(h*e for h, e in zip(multipliers, equations))-1, *params, extension=r)
    assert residual.is_zero
    out = {
        'scope': 'row-zero symmetric maximal-isotropic graph chart; not full L-gct-232',
        'field': 'Q(r), r^2=-2',
        'coefficient_order': [list(mon) for mon in polynomial.monoms()],
        'equations': [str(e) for e in equations],
        'multipliers': [str(e) for e in multipliers],
        'multiplier_degree_bound': degree,
        'identity': 'sum_i multipliers[i]*equations[i] = 1',
        'exact_identity_verified': True,
        'all_eight_charts': 'only product of three signs enters permanent; odd parity is r -> -r',
        'seconds': time.monotonic()-started
    }
    Path(__file__).with_name('rowzero-certificate.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['multiplier_degree_bound','exact_identity_verified','seconds']}))
    break
else:
    print('No certificate found through multiplier degree 3; this is not evidence of existence.')
