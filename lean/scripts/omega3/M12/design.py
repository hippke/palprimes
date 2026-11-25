"""M12 design prototype: exact-integer mirror of the planned Lean checker.
Geometric x grid xi_j = rho^j/85, rho=(Q+1)/Q; y grid y_s = 1 - rho^-s; caps gamma_k = rho^k - 1.
Fixed point: values v mean v/2^P (rounded up)."""
import sys, math, time
from fractions import Fraction as F
Q = int(sys.argv[1]); P = int(sys.argv[2]); R = int(sys.argv[3]); R1 = int(sys.argv[4]) if len(sys.argv) > 4 else 1
A, B = Q + 1, Q
ONE = 1 << P
def cdiv(a, b): return -((-a) // b)
pa = [1]; pb = [1]
for _ in range(4000): pa.append(pa[-1] * A); pb.append(pb[-1] * B)
xi = lambda j: F(pa[j], 85 * pb[j])
ys = lambda s: F(pa[s] - pb[s], pa[s])
gam = lambda k: F(pa[k] - pb[k], pb[k])
N = next(j for j in range(5000) if 3 * pa[j] >= 85 * pb[j])
Sy = next(s for s in range(5000) if 2 * pa[s] >= 3 * pb[s])
Shalf = next(s for s in range(5000) if pa[s] >= 2 * pb[s])
s3 = max(s for s in range(Sy + 1) if 3 * (pa[s] - pb[s]) <= pa[s])
def smax1(k): return next(t for t in range(6000) if (pa[t] - pb[t]) * pb[k] >= (pa[k] - pb[k]) * pa[t])
SM1 = [smax1(k) for k in range(Sy + 1)]
SMT = [min(v, Sy) for v in SM1]
def jlen(s): return next(J for J in range(N + 1) if J == N or pa[J + s + 1] >= 85 * pb[J] * (pa[s + 1] - pb[s + 1]))
JL = [jlen(s) for s in range(Sy)]
print('N', N, 'Sy', Sy, 'Shalf', Shalf, 's3', s3, file=sys.stderr)
# weights
W = [0] * Sy
for s in range(1, Sy):
    tot = 0
    for r in range(R):
        num = ONE * R * pa[s + 1]; den = (R * pa[s + 1] - (R * A - r) * pb[s]) * (R * A - r - 1)
        tot += cdiv(num, den)
    W[s] = tot
# base level phi1: rows k, entries j
t0 = time.time()
third = F(1, 3)
Bcol = []   # Bcol[s][j]
for s in range(s3, Shalf):
    row = []
    for j in range(N):
        x0, x1 = xi(j), xi(j + 1)
        top = (1 - x0) / 2
        if ys(s) >= top: row.append(0); continue
        tot = 0
        lo0 = max(ys(s), third); hi0 = min(ys(s + 1), top)
        for r in range(R1):
            lo = lo0 + (hi0 - lo0) * r / R1; hi = lo0 + (hi0 - lo0) * (r + 1) / R1
            d = lo * (1 - x1 - hi); assert d > 0
            q = (hi - lo) / d
            tot += cdiv(q.numerator * ONE, q.denominator)
        row.append(tot)
    Bcol.append(row)
def zadd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
acc = [[0] * N]
for row in Bcol: acc.append(zadd(acc[-1], row))
def pick1(k):
    t = SM1[k]   # cells s < t, s >= s3
    idx = max(0, min(t, Shalf) - s3)
    return acc[idx]
UP1 = [pick1(k) for k in range(Sy + 1)]
print('base time', time.time() - t0, file=sys.stderr)
def step(UP):
    accs = [[0] * N]
    for s in range(Sy):
        if s == 0: accs.append(accs[-1]); continue
        Rrow = UP[s + 1] + [0] * (2 * N)
        mx = [max(Rrow[j + s], Rrow[j + s + 1]) for j in range(JL[s])]
        sc = [cdiv(W[s] * v, ONE) for v in mx]
        accs.append(zadd(accs[-1], sc))
    return [accs[SMT[k]] for k in range(Sy + 1)]
levels = [None, UP1]
t0 = time.time()
for i in range(2, 83):
    levels.append(step(levels[-1]))
    if max(max(r) for r in levels[-1]) == 0: break
L = len(levels) - 1
print('levels', L, 'time', time.time() - t0, file=sys.stderr)
hbar = [sum(levels[i][Sy][j] for i in range(2, L + 1, 2)) for j in range(N)]
lev2 = [levels[2][Sy][j] for j in range(N)]
# output cells up to 1/4
J = next(j for j in range(N + 1) if 4 * pa[j] >= 85 * pb[j])   # xi_J >= 1/4
xs = [xi(j) for j in range(J)] + [F(1, 4)]
m = F(1, 85); k2 = F(9999, 1000); UU = F(83, 85); W1 = F(82, 85)
def Wq(t):
    if t <= m: return F(0)
    if t <= third: return min(k2 * t * t, t - m)
    if t <= UU: return t - m
    return W1
hp = F(0)
for j in range(J):
    a, b = xs[j], xs[j + 1]
    I = min((b - a) * (1 - m / b), k2 * (b * b - a * a) / 2)
    hp += F(hbar[j], ONE) * I
# exact base by mpmath
import mpmath as mp
mp.mp.dps = 30
Wm = lambda t: mp.mpf(0) if t <= 1/mp.mpf(85) else (min(9.999*t*t, t - 1/mp.mpf(85)) if t <= mp.mpf(1)/3 else (t - 1/mp.mpf(85) if t <= mp.mpf(83)/85 else mp.mpf(82)/85))
disc = mp.sqrt(1 - 4 * mp.mpf('9.999') / 85); t1 = (1 - disc) / (2 * mp.mpf('9.999')); t2 = (1 + disc) / (2 * mp.mpf('9.999'))
I1 = mp.quad(lambda t: (mp.mpf(82)/85 - Wm(t)) / ((1 - t) * t), [0.5, mp.mpf(83)/85])
I2 = mp.quad(lambda t: Wm(t) / ((1 - t) * t), [1/mp.mpf(85), t1, t2, mp.mpf(1)/3, 0.5])
base = -I1 + I2
print('Q', Q, 'P', P, 'R', R, 'R1', R1, 'N', N, 'J', J, 'Sy', Sy, 'L', L)
print('I1', mp.nstr(I1, 12), 'I2', mp.nstr(I2, 12), 'base', mp.nstr(base, 12))
print('hpart', float(hp), 'Mlow', float(base - hp))
print('hbar[0..5]', [float(F(h, ONE)) for h in hbar[:5]], 'max', float(F(max(hbar), ONE)))
import pickle
pickle.dump(dict(hbar=hbar, lev2=lev2, N=N, J=J, Q=Q, P=P), open(f'hbar_Q{Q}_R{R}_R1{R1}.pkl', 'wb'))
