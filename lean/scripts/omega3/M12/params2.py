import sys
from fractions import Fraction as F
A, B, M = map(int, sys.argv[1:4])
def vnum(s): return A**(s // M) * (M * B + (s % M) * (A - B))
def vden(s): return B**(s // M) * (M * B)
y = lambda s: F(vnum(s) - vden(s), vnum(s))
xi = lambda j: F(A**j, 85 * B**j)
N = next(j for j in range(10000) if xi(j) >= F(1, 3))
Sy = next(s for s in range(100000) if y(s) >= F(1, 3))
Sh = next(s for s in range(100000) if y(s) >= F(1, 2))
S3 = max(s for s in range(Sy + 1) if y(s) <= F(1, 3))
J = next(j for j in range(N + 1) if xi(j) >= F(1, 4))
print(f'⟨{A}, {B}, {M}, {N}, {Sy}, {Sh}, {S3}⟩ J={J} y1={float(y(1)):.5f}')
