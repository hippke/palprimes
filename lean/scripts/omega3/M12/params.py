import sys
from fractions import Fraction as F
Q, M = int(sys.argv[1]), int(sys.argv[2]); A = Q + 1
def vnum(s): return A**(s // M) * (M * Q + s % M)
def vden(s): return Q**(s // M) * (M * Q)
y = lambda s: F(vnum(s) - vden(s), vnum(s))
xi = lambda j: F(A**j, 85 * Q**j)
N = next(j for j in range(10000) if xi(j) >= F(1, 3))
Sy = next(s for s in range(100000) if y(s) >= F(1, 3))
Sh = next(s for s in range(100000) if y(s) >= F(1, 2))
S3 = max(s for s in range(Sy + 1) if y(s) <= F(1, 3))
J = next(j for j in range(N + 1) if xi(j) >= F(1, 4))
print('N', N, 'SY', Sy, 'SH', Sh, 'S3', S3, 'J', J, 'xi(J-1)', float(xi(J-1)), 'y1', float(y(1)))
