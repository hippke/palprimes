"""Plausibility check of the Lemma A definitions (S08, S09, M02) at finite level: lamA (Omega3/DefsSieve.lean) for b = 5,
z = sqrt x = 1000 and 3000, eta = 0 (Selberg) and a step function; compares lambda_1 + lambda_q with g_eta(u) and
Q(lambda) G(z) with c_eta. Errors O(1/log z) (about 0.1) are expected; the point is the normalisation and the signs."""
import sys, math
import numpy as np
from math import gcd
from scipy import integrate
out = []
def log(s): print(s); out.append(s)
r = 120
def setup(z):
    N = math.ceil(z)
    n = np.arange(N)
    spf = np.zeros(N, dtype=int)
    for p in range(2, N):
        if spf[p] == 0:
            spf[p::p][spf[p::p] == 0] = p
    def pf(k):
        res = []
        while k > 1:
            p = spf[k]; res.append(p)
            while k % p == 0: k //= p
        return res
    mu = np.zeros(N, dtype=int); phi = np.zeros(N); sqf = np.zeros(N, dtype=bool)
    for k in range(1, N):
        f = pf(k); kk = k; ok = True
        for p in f:
            kk //= p
            if kk % p == 0: ok = False
        sqf[k] = ok; mu[k] = (-1) ** len(f) if ok else 0
        phi[k] = k * np.prod([1 - 1 / p for p in f]) if f else 1
    return N, pf, mu, phi, sqf
def ev(s, u):
    acc = 0.0
    for a, v in s:
        if a <= u: acc = v
    return acc
def lam_vec(z, s, cache):
    N, pf, mu, phi, sqf = cache
    L = [k for k in range(1, N) if k < z]
    gS = np.array([0.0] + [1 / phi[k] if sqf[k] and gcd(k, r) == 1 else 0.0 for k in range(1, N)])
    G = gS[1:].sum()
    etaQ = lambda q: ev(s, math.log(q) / math.log(z)) / G
    etaK = np.array([0.0] + [sum(etaQ(q) for q in pf(k)) for k in range(1, N)])
    nu = (1 + (gS * etaK).sum()) / G
    yk = mu * gS * (nu - etaK)
    lam = np.zeros(N)
    for d in range(1, N):
        if gcd(d, r) != 1: continue
        ks = np.arange(d, N, d)
        lam[d] = d * (mu[ks // d] * yk[ks]).sum()
    return lam, G
def Ahat(s, x):
    if x <= 0: return 0.0
    pts = sorted(set([0.0, x] + [a for a, _ in s if 0 < a < x]))
    return sum(integrate.quad(lambda v: ev(s, v) * (x - v) / v, pts[i], pts[i + 1])[0] for i in range(len(pts) - 1))
def gEta(s, u): return 1 - (1 + Ahat(s, 1)) * (1 - u) + Ahat(s, 1 - u) + ev(s, u) * (1 - u)
def cEta(s):
    edges = sorted(set([1e-12, 1.0] + [a for a, _ in s]))
    I1 = sum(integrate.quad(lambda u: ev(s, u) ** 2 * (1 - u) / u, edges[i], edges[i + 1])[0] for i in range(len(edges) - 1))
    I2 = integrate.dblquad(lambda u2, u1: ev(s, u1) * ev(s, u2) * min(1, (1 - u1) / u1 * (1 - u2) / u2), 1e-9, 1, 1e-9, 1, epsabs=1e-7)[0]
    return 1 + I1 - I2
steps = {"eta=0": [], "step A": [(0.2, 0.15), (0.6, 0.0)], "step B": [(0.05, -0.1), (0.3, 0.2), (0.7, 0.05)]}
for z in (1000, 3000):
    cache = setup(z)
    for name, s in steps.items():
        lam, G = lam_vec(z, s, cache)
        qs = [q for q in (11, 31, 101, 307, 503, 907, 2003, 2999) if q < z]
        diffs = [lam[1] + lam[q] - gEta(s, math.log(q) / math.log(z)) for q in qs]
        line = f"z={z} {name}: lambda_1={lam[1]:.12f}, max|lambda_d|={np.abs(lam).max():.3f}, (lambda_1+lambda_q) - g_eta(u) at q={qs}: " + ", ".join(f"{d:+.3f}" for d in diffs)
        if z == 1000:
            idx = np.nonzero(lam)[0]
            Q = 0.0
            for d1 in idx:
                l = (d1 * idx) // np.gcd(d1, idx)
                rho = np.array([1.0 if gcd(int(v), r) == 1 else 0.0 for v in l])
                Q += lam[d1] * (lam[idx] * rho / l).sum()
            line += f"; Q*G = {Q * G:.4f} vs c_eta = {cEta(s):.4f}"
        log(line)
open(sys.argv[1], 'w').write("\n".join(out) + "\n")
