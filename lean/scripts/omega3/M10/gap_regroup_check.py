"""M10 (Greaves Lemma 11) gap decomposition, base b = 5 (rho(p) = 0 for p | 120).
gap(y) = M*(y^U) - E11(y) = sum_{p < sqrt y} w(p) * Delta_p  (the W(1) part and the p >= sqrt y part are exact identities)
Delta_p = (-H_p) - E_p,  -H_p = g(p) sum_{d1} mu(d1) g(d1) chi_y(d1) chi^-_y(d1 p) T^{eps(d1)}(y/(p d1), p)   (exact)
S_p     = g(p) sum_{d1} mu(d1) g(d1) chi_y(d1) chi^-_y(d1 p) T9sum(y/(p d1), p, eps(d1))   (Lemma 9 replacement)
L9_p    = -H_p - S_p   (Lemma 9 errors),  X_p = S_p - E_p  (terms with (d1, t) > 1, Lemma 10 is exact)
Usage: python3 gap_decomp.py LOG y1 y2 ..."""
import sys, math, bisect
from functools import lru_cache
import numpy as np
out = []
def log(s): print(s, flush=True); out.append(s)
U = 83/85; m = 1/85; W1 = 82/85; k2 = 9.999
def Wf(t):
    if t <= m: return 0.0
    if t <= 1/3: return min(k2*t*t, t - m)
    if t <= U: return t - m
    return W1
YS = [float(a) for a in sys.argv[2:]]
YMAX = max(int(max(YS) ** 0.5) * 4, 10**6)
sv = np.ones(YMAX + 1, dtype=bool); sv[:2] = False
for q in range(2, int(YMAX**0.5) + 1):
    if sv[q]: sv[q*q::q] = False
PR = [int(q) for q in np.nonzero(sv)[0] if 120 % q]
PRa = np.array(PR, dtype=float)
INV = np.concatenate([[0.0], np.cumsum(1/PRa)])
logV = np.concatenate([[0.0], np.cumsum(np.log1p(-1/PRa))])
def idx_lt(x): return bisect.bisect_left(PR, x)
def V(w): return math.exp(logV[idx_lt(w)])
def sum_inv(a, bnd):
    i, j = idx_lt(a), idx_lt(bnd)
    return INV[j] - INV[i] if j > i else 0.0

@lru_cache(maxsize=None)
def Tpm(y, w, plus):
    """T^{+-}(y, w) = sum_{d | P(w)} mu(d) g(d) chi^{+-}_y(d); chi^+ constrains odd positions, chi^- even ones."""
    tot = 0.0
    con = (lambda i: i % 2 == 1) if plus else (lambda i: i % 2 == 0)
    def rec(P, last, i, sgn):
        nonlocal tot
        tot += sgn / P
        hi = min(last, w); nxt = i + 1
        if con(nxt):
            k = idx_lt(min(hi, (y / P) ** (1/3)))
            for j in range(k - 1, -1, -1): rec(P * PR[j], PR[j], nxt, -sgn)
        else:
            cut = min(hi, y / (P * 343.0)); k = idx_lt(cut)
            for j in range(k - 1, -1, -1): rec(P * PR[j], PR[j], nxt, -sgn)
            if hi > cut: tot += -sgn / P * sum_inv(max(cut, 0), hi)
    rec(1, float('inf'), 0, 1)
    return tot

def sigmaP(eta):
    key = round(eta, 6)
    return Tpm(key, key ** (1/3), True)

def T9sum_nc(eta, p, plus, d1set):
    """as T9sum, restricted to t sharing a prime with d1."""
    tot = 0.0
    def rec(P, last, q1, nu, shared):
        nonlocal tot
        if (nu % 2 == 0) == plus and shared:
            tot += sigmaP(eta / P) / P
        hi = min(math.sqrt(eta), last) if P == 1 else min(last, eta / (P * q1))
        k = idx_lt(hi)
        for j in range(k - 1, -1, -1):
            r = PR[j]
            if r <= p: break
            rec(P * r, r, q1 if P > 1 else r, nu + 1, shared or (r in d1set))
    rec(1, float('inf'), None, 0, False)
    return tot

def T9sum(eta, p, plus):
    """sum over squarefree t, all primes > p, q(t) t < eta, nu(t) even (plus) / odd, of g(t) sigma+(eta/t)."""
    tot = 0.0
    def rec(P, last, q1, nu):
        nonlocal tot
        if (nu % 2 == 0) == plus:
            tot += sigmaP(eta / P) / P
        # next prime r < last, r > p, (P r) * q1' < eta where q1' = q1 (or r if P = 1)
        if P == 1:
            hi = min(math.sqrt(eta), last)
        else:
            hi = min(last, eta / (P * q1))
        k = idx_lt(hi)
        for j in range(k - 1, -1, -1):
            r = PR[j]
            if r <= p: break
            rec(P * r, r, q1 if P > 1 else r, nu + 1)
    rec(1, float('inf'), None, 0)
    return tot

def Vbig(y):
    if y > 1e9: return Vbig(1e9) * math.log(1e9) / math.log(y)   # Mertens tail (rel. error < 1e-4)
    if y <= YMAX: return V(y)
    lv = logV[-1]; base = np.array(PR[:idx_lt(int(y**0.5)+2)], dtype=np.int64); seg = 10**7; lo = YMAX + 1
    while lo <= y:
        hi = min(int(y), lo + seg - 1); a = np.ones(hi - lo + 1, dtype=bool)
        for q in [2, 3, 5] + list(base):
            q = int(q)
            if q * q > hi: break
            st = max(q * q, ((lo + q - 1) // q) * q); a[st - lo::q] = False
        ps = np.nonzero(a)[0] + lo
        ps = ps[ps < y]
        lv += np.log1p(-1.0 / ps).sum(); lo = hi + 1
    return math.exp(lv)
maxdiff = 0.0
def run(y):
    z = y ** U; Vy = Vbig(y); ly = math.log(y)
    wy = lambda q: Wf(math.log(q) / ly)
    sq = math.sqrt(y)
    rows = []
    gap = 0.0; gapL9 = 0.0; gapX = 0.0
    for jp in range(0, idx_lt(sq)):
        p = PR[jp]; wp = wy(p)
        if wp == 0: continue
        negH = 0.0; S = 0.0
        # d1 chains: primes in (p, z) decreasing, all positions constrained (chi_y), extra chi^- check at p
        Xd = 0.0
        def rec(P, last, nu, sgn, prs=()):
            nonlocal negH, S, Xd
            ok = True
            if (nu + 1) % 2 == 0 and P * p**3 >= y: ok = False
            if ok:
                eta = y / (p * P); plus = (nu % 2 == 0)
                negH += sgn / P * Tpm(eta, float(p), plus)
                S += sgn / P * T9sum(eta, p, plus)
                if prs: Xd += sgn / P * T9sum_nc(eta, p, plus, set(prs))
            k = idx_lt(min(last, z, (y / P) ** (1/3)))
            for j in range(k - 1, -1, -1):
                q = PR[j]
                if q <= p: break
                rec(P * q, q, nu + 1, -sgn, prs + (q,))
        rec(1, float('inf'), 0, 1)
        negH /= p; S /= p; Xd /= p
        # E_p
        inner = 0.0
        def recn(P, last, i):
            nonlocal inner
            if (i + 1) % 2 == 0:
                lo = max(p + 1, (y / P) ** (1/3)); hi = min(last, math.sqrt(y / (p * P)))
                for jj in range(idx_lt(lo), idx_lt(hi)):
                    q = PR[jj]
                    if q <= p or P * q**3 < y: continue
                    n = P * q
                    if n * q < y / p: inner += sigmaP(y / (p * n)) / n
            k = idx_lt(min(last, (y / P) ** (1/3)))
            for jj in range(k - 1, -1, -1):
                q = PR[jj]
                if q <= p: break
                recn(P * q, q, i + 1)
        recn(1, float('inf'), 0)
        E = (sigmaP(y / p) - inner) / p
        D = negH - E; L9 = negH - S; X = S - E
        global maxdiff
        maxdiff = max(maxdiff, abs(X - Xd) * p / V(p))
        gap += wp * D; gapL9 += wp * L9; gapX += wp * X
        rows.append((p, wp, D, L9, X, V(p)))
    log(f"   regrouping check: max_p p|X_p - X_p(direct, (d1,t)>1)|/V(p) = {maxdiff:.2e}")
    log(f"y = {y:.0e}: V(y) = {Vy:.5f}, y^m = {y**m:.3f}; gap/V = {gap/Vy:+.5f} (Lemma 9 errors {gapL9/Vy:+.5f}, (d1,t)>1 terms {gapX/Vy:+.5f})")
    log("   p   w(p)   p*Delta_p/V(p)  p*L9_p/V(p)  p*X_p/V(p)   cumulative w*Delta/V(y) from p upward")
    cum = 0.0; cums = []
    for r in reversed(rows):
        cum += r[1] * r[2]; cums.append(cum)
    cums = cums[::-1]
    for r, c in zip(rows, cums):
        if r[0] < 60 or r is rows[-1] or r[0] in (97, 199, 307, 401, 503, 601, 701, 809, 907):
            log(f"  {r[0]:4d} {r[1]:.4f}  {r[0]*r[2]/r[5]:+.4f}        {r[0]*r[3]/r[5]:+.4f}       {r[0]*r[4]/r[5]:+.4f}      {c/Vy:+.5f}")
    for c0 in (0.1, 0.15, 0.2, 0.25):
        g = sum(r[1]*r[2] for r in rows if r[0] >= y**c0)
        log(f"   part from p >= y^{c0} (= {y**c0:.1f}): {g/Vy:+.5f} V(y)")
for y in YS:
    run(y)
open(sys.argv[1], 'w').write("\n".join(out) + "\n")
