"""Small exact algebra checks supporting the scoped L-gct-232 assessment.

No numerical arithmetic, no Lean claim, and no assertion that the restricted
families exhaust the task's arbitrary complex symmetric subspaces.
"""
import itertools
import json
import resource
import time

resource.setrlimit(resource.RLIMIT_CPU, (30, 31))
resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
import sympy as s

started = time.monotonic()

def permanent(M):
    return s.expand(sum(s.prod(M[i, perm[i]] for i in range(M.rows))
                        for perm in itertools.permutations(range(M.rows))))

# Verify the row-zero cubic Taylor identity on all symmetric row-zero 4x4
# matrices.  H has independent columns spanning the sum-zero hyperplane.
H = s.Matrix([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]])
u = s.symbols('A B C D E F')
A, B, C, D, E, F = u
U = s.Matrix([[A, D, E], [D, B, F], [E, F, C]])
T = H * U * H.T
assert H.T * H == 4 * s.eye(3)
assert s.ones(1, 4) * H == s.zeros(1, 3)
assert s.expand(sum(T[i, j]**2 for i in range(4) for j in range(4))
                - 16 * s.trace(U * U)) == 0
third = 0
for rows in itertools.combinations(range(4), 3):
    for cols in itertools.combinations(range(4), 3):
        third += permanent(T.extract(rows, cols))
assert s.expand(third - s.Rational(2, 3)
                * sum(T[i, j]**3 for i in range(4) for j in range(4))) == 0
assert s.expand(third - 64 * permanent(U)) == 0

# The natural S4-standard family is already excluded by coefficients 2 and 3.
x, y, z, a, b, t = s.symbols('x y z a b t')
v = [x, y, z, -x-y-z]
S = s.Matrix(4, 4, lambda i, j: a*v[i] if i == j else b*(v[i]+v[j]))
P = s.Poly(permanent(s.ones(4)+t*S)-24, t)
f = a*a + 8*a*b + 4*b*b
g = a**3 + 6*a*a*b + 12*a*b*b - 8*b**3
assert P.nth(1) == 0
assert s.expand(P.nth(2) + 2*f*(x*x+x*y+x*z+y*y+y*z+z*z)) == 0
assert s.expand(P.nth(3) + g*(x+y)*(x+z)*(y+z)) == 0
assert s.expand(g-(a-2*b)*f-24*a*b*b) == 0
assert s.expand(24*b*b*f-(a+8*b)*(g-(a-2*b)*f)-96*b**4) == 0

# Quadratic branches in the single-block-direction calculation, restricted
# to matrices whose opposite principal 2x2 block is zero.
c, d, f0, g0, p, q, m, n = s.symbols('c d f0 g0 p q m n')
Q = c*c+2*c*d-6*c*f0-2*c*g0+d*d-2*d*f0-6*d*g0+f0*f0+2*f0*g0+g0*g0
Qpq = s.expand(Q.subs({c:(p+m)/2, d:(p-m)/2, f0:(q+n)/2, g0:(q-n)/2}))
assert s.expand(Qpq - (-2*m*n+p*p-4*p*q+q*q)) == 0
determinants = []
for k in [s.Integer(1), 2*s.sqrt(2)-3]:
    det = s.simplify(s.hessian(Qpq.subs(p, k*q), (q, m, n)).det())
    assert det != 0
    determinants.append(str(det))

print(json.dumps({
    'exact_checks_passed': [
        'Hadamard coordinates span symmetric row-zero matrices',
        'quadratic coefficient is the Frobenius square sum in row-zero case',
        'cubic coefficient is (2/3) times entrywise cube sum in row-zero case',
        'cubic coefficient is 64 times permanent of the symmetric 3x3 Hadamard coordinate matrix',
        'S4-standard-family quadratic and cubic formulas',
        'S4-standard-family explicit elimination identities',
        'single-block zero-opposite-block quadratic branch ranks'],
    'branch_hessian_determinants': determinants,
    'seconds': time.monotonic()-started,
    'scope': 'restricted algebraic checks only; full L-gct-232 remains open'
}, indent=2))
