"""Fine grid (rho=A/B) for level 1 + level-2 top row; coarse grid rho^m for levels 1..LC (rest = even levels 4..LC);
crude tail (1/x) sum_{i even > LC} 4^i/i!. Exact-integer mirror (fixed point 2^P), output cells = fine cells up to 1/4."""
import sys, time, math
from fractions import Fraction as F
Qf, Mf, mm_, Mc, LC = map(int, sys.argv[1:6]); P = 64; ONE = 1 << P
def cdiv(a, b): return -((-a) // b)
def fup(q): return cdiv(q.numerator * ONE, q.denominator)
def build(A, B, M):
    rho = F(A, B)
    N = 0
    while F(A**N, 85 * B**N) < F(1, 3): N += 1
    xi = [F(A**j, 85 * B**j) for j in range(N + 1)]
    v = []; s = 0
    while True:
        base = rho**s
        for r in range(M): v.append(base * (1 + (rho - 1) * F(r, M)))
        if base >= 2: break
        s += 1
    ys = [1 - 1 / vv for vv in v]; gam = [vv - 1 for vv in v]
    Sy = next(i for i in range(len(v)) if ys[i] >= F(1, 3))
    s3 = max(i for i in range(Sy + 1) if ys[i] <= F(1, 3))
    Sh = next(i for i in range(len(v)) if ys[i] >= F(1, 2))
    SM1 = [next(t for t in range(len(v)) if ys[t] >= gam[k]) for k in range(Sy + 1)]
    SMT = [min(t, Sy) for t in SM1]
    JL = [next((J for J in range(N + 1) if xi[J] >= ys[sg + 1]), N) for sg in range(Sy)]
    W = [0] * Sy
    for sg in range(1, Sy): W[sg] = fup((v[sg + 1] - v[sg]) / (v[sg] - 1))
    third = F(1, 3)
    def zadd(a, b):
        n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
    acc = [[0] * N]
    for sg in range(s3, Sh):
        row = []
        for j in range(N):
            x0, x1 = xi[j], xi[j + 1]; top = (1 - x0) / 2
            if ys[sg] >= top: row.append(0); continue
            lo = max(ys[sg], third); hi = min(ys[sg + 1], top)
            row.append(fup(max(hi - lo, 0) / (lo * (1 - x1 - hi))))
        acc.append(zadd(acc[-1], row))
    UP1 = [acc[max(0, min(SM1[k], Sh) - s3)] for k in range(Sy + 1)]
    def step(UP, toponly=False):
        accs = [[0] * N]
        for sg in range(Sy):
            s = sg // M
            if W[sg] == 0: accs.append(accs[-1]); continue
            Rrow = UP[sg + 1] + [0] * (2 * N + 2)
            sc = [cdiv(W[sg] * max(Rrow[j + s], Rrow[j + s + 1]), ONE) for j in range(JL[sg])]
            accs.append(zadd(accs[-1], sc))
        return [accs[SMT[k]] for k in range(Sy + 1)]
    return dict(N=N, xi=xi, Sy=Sy, UP1=UP1, step=step)
Af, Bf = Qf + 1, Qf
fg = build(Af, Bf, Mf)
t0 = time.time()
lev2 = fg['step'](fg['UP1'])
h2f = lev2[fg['Sy']]
cg = build(Af**mm_, Bf**mm_, Mc)
levs = [None, cg['UP1']]
for i in range(2, LC + 1): levs.append(cg['step'](levs[-1]))
restc = [sum(levs[i][cg['Sy']][J] for i in range(4, LC + 1, 2)) for J in range(cg['N'])]
xi = fg['xi']
J = next(j for j in range(fg['N'] + 1) if xi[j] >= F(1, 4))
xs = xi[:J] + [F(1, 4)]
m = F(1, 85); k2 = F(9999, 1000)
tailc = float(sum(F(4**i, math.factorial(i)) for i in range(LC + 1 + (LC % 2 == 1), 120, 2)))
hp2 = 0.0; hpr = 0.0; hpt = 0.0
for j in range(J):
    a, b = xs[j], xs[j + 1]
    I = float(min((b - a) * (1 - m / b), k2 * (b * b - a * a) / 2))
    hp2 += h2f[j] / ONE * I; hpr += restc[j // mm_] / ONE * I; hpt += tailc / float(a) * I
hp = hp2 + hpr + hpt
print("h2f", h2f[:3], "restc", restc[:3], len([r for r in restc]))
print(f'Qf {Qf} Mf {Mf} m {mm_} Mc {Mc} LC {LC} Nf {fg["N"]} SYf {fg["Sy"]} Nc {cg["N"]} SYc {cg["Sy"]} h2 {hp2:.7f} (loss {hp2-0.019111078:.2e}) rest {hpr:.7f} (loss {hpr-0.002654:.2e}) tail {hpt:.2e} hpart {hp:.7f} Mlow {0.0321844108171-hp:.6f}  time {time.time()-t0:.1f}')
