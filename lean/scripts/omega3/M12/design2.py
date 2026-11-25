"""M12 design v2: geometric x grid (ratio rho=(Q+1)/Q, xi_j = rho^j/85); fine y grid with M sub-cells per
geometric y cell: v_sig = rho^s (1 + r/(M Q)) (sig = sM + r), y_sig = 1 - 1/v_sig, caps gamma_sig = v_sig - 1.
Cover of x' = x/(1-y) for y in fine cell sig=(s,r): cells j+s, j+s+1. Fixed point 2^P, rounding up."""
import sys, time, pickle
from fractions import Fraction as F
Q, P, M, R, R1 = map(int, sys.argv[1:6])
A, B = Q + 1, Q; ONE = 1 << P
def cdiv(a, b): return -((-a) // b)
def fup(q): return cdiv(q.numerator * ONE, q.denominator)
rho = F(A, B)
N = 0
while F(A**N, 85 * B**N) < F(1, 3): N += 1
xi = [F(A**j, 85 * B**j) for j in range(N + 1)]
v = []
s = 0
while True:
    base = rho**s
    for r in range(M): v.append(base * (1 + F(r, M * Q)))
    if base >= 2: break
    s += 1
ys = [1 - 1 / vv for vv in v]; gam = [vv - 1 for vv in v]
nsig = len(v) - 1
Sy = next(i for i in range(nsig) if ys[i] >= F(1, 3))      # fine cells sig < Sy cover y <= 1/3
s3 = max(i for i in range(Sy + 1) if ys[i] <= F(1, 3))
Sh = next(i for i in range(nsig) if ys[i] >= F(1, 2))
SM1 = [next(t for t in range(nsig + 1) if ys[t] >= gam[k]) for k in range(Sy + 1)]
SMT = [min(t, Sy) for t in SM1]
JL = [next((J for J in range(N + 1) if xi[J] >= ys[sg + 1]), N) for sg in range(Sy)]
print('N', N, 'Sy', Sy, 'Sh', Sh, 's3', s3, file=sys.stderr)
# weights: int over fine cell of dy/(y(1-y)), R uniform sub-cells (sup of integrand * length)
W = [0] * Sy
for sg in range(Sy):
    a, b = ys[sg], ys[sg + 1]
    if a <= 0: continue
    tot = 0
    for r in range(R):
        lo = a + (b - a) * r / R; hi = a + (b - a) * (r + 1) / R
        tot += fup((hi - lo) / (lo * (1 - hi)))
    W[sg] = tot
t0 = time.time()
third = F(1, 3)
def zadd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
acc = [[0] * N]
for sg in range(s3, Sh):
    row = []
    for j in range(N):
        x0, x1 = xi[j], xi[j + 1]; top = (1 - x0) / 2
        if ys[sg] >= top: row.append(0); continue
        lo0 = max(ys[sg], third); hi0 = min(ys[sg + 1], top); tot = 0
        for r in range(R1):
            lo = lo0 + (hi0 - lo0) * r / R1; hi = lo0 + (hi0 - lo0) * (r + 1) / R1
            d = lo * (1 - x1 - hi); assert d > 0
            tot += fup((hi - lo) / d)
        row.append(tot)
    acc.append(zadd(acc[-1], row))
UP1 = [acc[max(0, min(SM1[k], Sh) - s3)] for k in range(Sy + 1)]
print('base time', time.time() - t0, file=sys.stderr)
def step(UP):
    accs = [[0] * N]
    for sg in range(Sy):
        s = sg // M
        if W[sg] == 0: accs.append(accs[-1]); continue
        Rrow = UP[sg + 1] + [0] * (2 * N + 2)
        sc = [cdiv(W[sg] * max(Rrow[j + s], Rrow[j + s + 1]), ONE) for j in range(JL[sg])]
        accs.append(zadd(accs[-1], sc))
    return [accs[SMT[k]] for k in range(Sy + 1)]
levels = [None, UP1]; t0 = time.time()
for i in range(2, 83):
    levels.append(step(levels[-1]))
    if max(max(r) for r in levels[-1]) == 0: break
L = len(levels) - 1
print('levels', L, 'time', time.time() - t0, file=sys.stderr)
hbar = [sum(levels[i][Sy][j] for i in range(2, L + 1, 2)) for j in range(N)]
lev2 = [levels[2][Sy][j] for j in range(N)]
J = next(j for j in range(N + 1) if xi[j] >= F(1, 4))
xs = xi[:J] + [F(1, 4)]
m = F(1, 85); k2 = F(9999, 1000)
hp = F(0); hp2 = F(0)
for j in range(J):
    a, b = xs[j], xs[j + 1]
    I = min((b - a) * (1 - m / b), k2 * (b * b - a * a) / 2)
    hp += F(hbar[j], ONE) * I; hp2 += F(lev2[j], ONE) * I
base = 0.0321844108171
print(f'Q {Q} M {M} R {R} R1 {R1} N {N} J {J} Sy {Sy} L {L} hpart {float(hp):.7f} h2part {float(hp2):.7f} loss2 {float(hp2)-0.019111078:.3e} rest {float(hp-hp2):.6f} Mlow {base-float(hp):.6f}')
pickle.dump(dict(hbar=hbar, lev2=lev2, N=N, J=J, Q=Q, P=P, M=M), open(f'h2_Q{Q}_M{M}.pkl', 'wb'))
