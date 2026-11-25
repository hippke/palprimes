import sys, pickle, mpmath as mp
from fractions import Fraction as F
mp.mp.dps = 20
d = pickle.load(open(sys.argv[1], 'rb'))
Q, P, J = d['Q'], d['P'], d['J']; ONE = 1 << P
def phi1(x, c):
    if x >= mp.mpf(1)/3: return 0
    cc = min(c, (1 - x) / 2)
    if cc <= mp.mpf(1)/3: return 0
    return mp.log(cc * (2 - 3 * x) / (1 - x - cc)) / (1 - x)
def h2(x):
    lo = max(x, mp.mpf(1)/4)
    if lo >= mp.mpf(1)/3: return 0
    return mp.quad(lambda y: phi1(x / (1 - y), y / (1 - y)) / (y * (1 - y)), [lo, mp.mpf(1)/3])
k2 = mp.mpf(9999)/1000; m = mp.mpf(1)/85
def Wm(t): return min(k2*t*t, t - m)
ex = mp.quad(lambda t: Wm(t) * h2(t) / t, [m, 0.0136, 0.0864, 0.25], maxdegree=6)
A, B = Q + 1, Q
xs = [F(A**j, 85 * B**j) for j in range(J)] + [F(1, 4)]
mf = F(1, 85); k2f = F(9999, 1000)
hp2 = F(0); hpa = F(0)
for j in range(J):
    a, b = xs[j], xs[j + 1]
    I = min((b - a) * (1 - mf / b), k2f * (b * b - a * a) / 2)
    hp2 += F(d['lev2'][j], ONE) * I; hpa += F(d['hbar'][j], ONE) * I
print('Q', Q, 'exact int W h2/t', mp.nstr(ex, 10), 'table h2 part', float(hp2), 'loss2', float(hp2) - float(ex), 'total hpart', float(hpa), 'rest', float(hpa - hp2))
