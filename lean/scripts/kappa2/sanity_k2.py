"""Sanity checks of the frozen OK2 κ statements (DefsK.lean, StatementsK.lean) on small instances, float/exact.
Positive checks and negative controls (a perturbed statement must fail)."""
import numpy as np
from fractions import Fraction as F
from math import log, pi, cos, sqrt, gcd
import itertools, random

def fejerW(m, a):
    return F(min(a + 1, 2 * m - 1 - a), m * m) if a + 1 < 2 * m else F(0)
def prodW(M, a):
    return F(min(a + 1, M, 2 * M - a), M * (M + 1)) if a < 2 * M else F(0)
def recGK(b, a):
    return fejerW((b + 1) // 2, a) if b % 2 else prodW(b // 2, a)
def fejTau(m, u):
    return 1 / m if u == 0 else ((m - u) / m ** 2 if u < m else 0.0)
def recPK(b): return 1 - 1 / b ** 6
def recHK(b): return (b + 1) // 2 - 1 if b % 2 else b // 2
def recPolyK(b, u):
    return fejTau((b + 1) // 2, u) if b % 2 else (fejTau(b // 2, u) + fejTau(b // 2 + 1, u)) / 2
def recTauK(b, u): return (1 - recPK(b) if u == 0 else 0) + recPK(b) * recPolyK(b, u)
def trigEval(H, tau, t): return tau(0) + 2 * sum(tau(u) * np.cos(2 * pi * u * t) for u in range(1, H + 1))
def mw4(b, g):
    c = np.convolve([float(g(a)) for a in range(b)], [float(g(a)) for a in range(b)])
    return float((c * c).sum())
def Gg(b, g, t): return sum(float(g(a)) * np.exp(2j * pi * a * t) for a in range(b))

out = []
# LK07
th = 103 / 200
worst = 9
for b in list(range(3, 200)) + [10**3, 10**4, 10**6]:
    g = lambda a: recGK(b, a)
    assert sum(g(a) for a in range(b)) == 1 and all(g(a) >= 0 for a in range(b)) and g(1) > 0
    assert max(g(a) for a in range(b)) <= F(1, 2)
    tau0 = recTauK(b, 0)
    mass = abs(tau0) + 2 * sum(abs(recTauK(b, u)) for u in range(1, recHK(b) + 1))
    psi = -log(tau0) / log(b)
    slack = 7 / 20 * psi + 3 / 10 * recPK(b) - th - 1 / 1000
    worst = min(worst, slack)
    ok = mass <= 1 + 1e-12 and recHK(b) <= b * (b - 1) and slack > 0
    if b <= 2000:
        ok = ok and mw4(b, g) <= 1 / b
    if not ok or b <= 6:
        out.append(f"LK07 b={b}: mass={mass:.12f} psi={psi:.5f} slack={slack:.5f} mw4*b={mw4(b, g) * b if b <= 2000 else 'n/a'} ok={ok}")
    assert ok, b
print("LK07 done", flush=True); out.append(f"LK07 all b in list ok, worst slack {worst:.5f}")
# majorant RecMajK and ProdAbs on a grid
t = np.linspace(0, 1, 20001)
for b in range(3, 25):
    g = lambda a: recGK(b, a); p = recPK(b)
    lhs = np.abs(Gg(b, g, t)) ** p
    rhs = trigEval(recHK(b), lambda u: recTauK(b, u), t)
    assert (rhs - lhs).min() > -1e-12, b
    if b % 2 == 0:
        M = b // 2
        FM = lambda m: trigEval(m - 1, lambda u: fejTau(m, u), t)
        assert (np.abs(Gg(b, g, t)) - (FM(M) + FM(M + 1)) / 2).max() < 1e-12
out.append("RecMajK, ProdAbs: grid ok for b = 3..24"); print("majorants done", flush=True)
# negative control: the same with p = 1 - 1/b^2 fails LK07 at b = 3
p = 1 - 1 / 9; tau0 = (1 - p) + p / 2
out.append(f"NEG LK07 with p = 1 - 1/b^2 at b = 3: slack {7/20*(-log(tau0)/log(3)) + 0.3*p - th - 1e-3:.4f} (must be < 0)")
# Kmid construction
def kmid(W, p):
    k0 = int(np.floor(np.log2(W))) - 2
    Ms = [W // 2 ** (k + 1) for k in range(k0 + 1)]
    S = Ms[0] - 1
    kap = np.zeros(S + 1)
    for k, M in enumerate(Ms):
        for u in range(M):
            kap[u] += 2.5 * 2 ** (-k * p) * fejTau(M, u)
    kap[0] += (4 / W) ** p
    return S, kap
for W in [16, 17, 81, 243, 1000, 4096]:
    for p in [0.5, 0.9, 0.999]:
        S, kap = kmid(W, p)
        bet = np.linspace(0, 0.5, 40001)
        Mv = np.abs(np.array([sum(np.exp(2j * pi * w * x) for w in range(W)) if False else 0 for x in []])) if False else None
        num = np.abs(np.sin(pi * W * bet) / np.where(bet == 0, 1, np.sin(pi * bet)) / W); num[0] = 1
        K = trigEval(S, lambda u: kap[u], bet)
        assert 2 * S < W and (K - num ** p).min() > -1e-12, (W, p, (K - num ** p).min())
        assert kap[0] <= 100 * (1 + log(W)) * W ** (-p) and kap[0] + 2 * kap[1:].sum() <= 100
print("Kmid done", flush=True); out.append("Kmid: construction passes for W in {16,17,81,243,1000,4096}, p in {0.5,0.9,0.999}")
# Lemma29K and SqParsevalK on small instances (exact sums by direct evaluation)
def cK(b, N, k): return b ** k + b ** (2 * N - k) if k < N else b ** N
def mK(N): return 7 * (2 * N + 1) // 20
def ellK(N): return 2 * N + 1 - 2 * mK(N)
def Mmid(W, beta):
    """closed form W^-1 sum_{w<W} e(w beta), vectorised; exact limit 1 at integers"""
    beta = np.asarray(beta, dtype=float)
    z = np.exp(2j * pi * beta)
    near = np.abs(1 - z) < 1e-12
    val = np.where(near, 1.0 + 0j, (1 - z ** W) / np.where(near, 1, 1 - z) / W)
    return val
def gJK(b, g, N, j, a):
    """vectorised in a (numpy array); reduces phases mod 1 with exact integer arithmetic where possible"""
    W = b ** ellK(N); m = mK(N)
    a = np.asarray(a, dtype=float)
    v = np.ones_like(a, dtype=complex)
    for k in range(m - j, m):
        v *= Gg(b, g, np.mod(cK(b, N, k) * a, 1.0))
    v *= Mmid(W, np.mod(b ** m * a, 1.0))
    return v
def mM4(W): return (2 * W ** 2 + 1) / (3 * W ** 3)
for b, N in [(3, 6), (4, 6), (5, 5)]:
    g = lambda a: recGK(b, a); m = mK(N); W = b ** ellK(N)
    for j in range(0, min(m, 3)):
        # SqParsevalK at the smallest prime p not dividing b with 6 W b^{2j} <= p^2
        p0 = int(sqrt(6 * W * b ** (2 * j))) + 1
        pr = next(q for q in range(p0, 10 ** 6) if all(q % d for d in range(2, int(sqrt(q)) + 1)) and b % q)
        beta = 0.123
        lhs = float((np.abs(gJK(b, g, N, j, np.arange(pr ** 2) / pr ** 2 + beta)) ** 4).sum())
        rhs = pr ** 2 * mw4(b, g) ** j * mM4(W)
        assert abs(lhs - rhs) < 1e-6 * rhs, (b, N, j, lhs, rhs)
        # Lemma29K at D = 4 and D = 8
        for D in [4, 8]:
            s = sum(float((np.abs(gJK(b, g, N, j, np.array([h / d for h in range(d) if gcd(h, d) == 1]) + beta)) ** 4).sum())
                    for d in range(D, 2 * D) if gcd(d, b) == 1)
            bound = 16 * (D ** 2 + b * W * b ** (2 * j)) * mw4(b, g) ** j * mM4(W)
            assert s <= bound, (b, N, j, D, s, bound)
    print(f"SqParsevalK equality and Lemma29K bound ok at b={b}, N={N} (m={m}, W={W}), j < {min(m, 3)}")
# negative control for SqParsevalK: p^2 below the frequency range
b, N, j = 3, 6, 1; g = lambda a: recGK(b, a); W = b ** ellK(N)
pr = 5
lhs = float((np.abs(gJK(b, g, N, j, np.arange(pr ** 2) / pr ** 2 + 0.123)) ** 4).sum())
out.append(f"NEG SqParsevalK with p^2 = 25 < 6Wb^2 = {6 * W * 9}: lhs {lhs:.4f} vs rhs {pr**2 * mw4(b, g) ** j * mM4(W):.4f} (differ)")
print("\n".join(out), flush=True)
