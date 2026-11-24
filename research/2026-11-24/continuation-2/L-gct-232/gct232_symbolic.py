"""Exact symbolic checks for a partial rigidity result, not L-gct-232 itself."""
import itertools
import sympy as s

x, y, z = s.symbols('x y z')
u = s.symbols('a b c d e f g h i j')
a, b, c, d, e, f, g, h, i, j = u
pairs = [(r, c) for r in range(4) for c in range(r, 4)]
C = s.zeros(4)
for k, (r, col) in enumerate(pairs):
    C[r, col] = C[col, r] = u[k]
A = s.zeros(4)
A[0, 1] = A[1, 0] = 1
A[0, 3] = A[3, 0] = -1
B = s.zeros(4)
B[0, 2] = B[2, 0] = 1
B[0, 3] = B[3, 0] = -1
M = s.ones(4) + x*A + y*B + z*C
per = s.expand(sum(s.prod(M[r, p[r]] for r in range(4))
                   for p in itertools.permutations(range(4))))
P = s.Poly(per-24, x, y, z)
linear = [s.factor(v) for k, v in P.terms() if k[2] == 1]
solution = next(iter(s.linsolve(linear, u)))
expected = (-2*b-2*c-2*d-9*j, b, c, d, j, j, j, j, j, j)
assert all(s.expand(v-w) == 0 for v, w in zip(solution, expected))
reduced = s.Poly(P.as_expr().subs(dict(zip(u, solution)), simultaneous=True), z)
q = 2*((b+c+d)**2-6*(b+c+d)*j-63*j**2)
cubic = 4*j*((b+c+d)**2-6*(b+c+d)*j-39*j**2)
quartic = 2*j**2*(b+c+d-9*j)*(b+c+d+3*j)
assert s.expand(reduced.as_expr()-q*z**2-cubic*z**3-quartic*z**4) == 0
assert s.expand(cubic-2*j*q-96*j**3) == 0
assert s.expand(q.subs(j, 0)-2*(b+c+d)**2) == 0
assert s.expand(P.as_expr().subs(dict(zip(u, (0,b,c,-b-c,0,0,0,0,0,0))), simultaneous=True)) == 0
root_two = s.sqrt(2)
block_A = s.zeros(4)
block_A[0, 0], block_A[1, 1] = root_two-1, -root_two-1
block_A[0, 1] = block_A[1, 0] = 1
block_B = s.zeros(4)
block_B[2, 2], block_B[3, 3] = root_two-1, -root_two-1
block_B[2, 3] = block_B[3, 2] = 1
block_M = s.ones(4)+x*block_A+y*block_B
block_per = s.expand(sum(s.prod(block_M[r, p[r]] for r in range(4))
                         for p in itertools.permutations(range(4))))
assert block_per == 24
print('Exact SymPy identities checked.')
print('Linear constraints:', linear)
print('General solution of linear constraints:', solution)
print('Remaining coefficients:', [s.factor(q), s.factor(cubic), s.factor(quartic)])
print('Certificate: cubic - 2*j*quadratic = 96*j^3.')
print('Scope: any extension of the displayed symmetric two-dimensional star space is trivial.')
print('An independent non-star two-dimensional block family also has permanent identically24.')
print('The general three-dimensional nonexistence statement remains unproved.')
