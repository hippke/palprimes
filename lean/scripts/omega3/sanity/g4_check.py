"""Finite-y plausibility check of the Greaves §4 transcriptions (items M07 = Lemma 8, M08 = Lemma 9, M10 = Lemma 11,
M11 = Lemma 12) for the density of base b = 5 (rho(p) = 0 for p | 120) and the weight of the route.
Exact sums (DFS over decreasing prime chains, prefix conditions h p(h)^2 < y on top-prefixes) of the objects defined in
Omega3/DefsSieve.lean: M1, M23, Mstar, Tpm, sigmaP, T9sum, E11. The lemmas are asymptotic (errors O(log^{-1/5} y) in
Greaves, in practice about 1/log y); a transcription error would show as an O(1) discrepancy in units of V(y)."""
import sys, math, bisect
from functools import lru_cache
import numpy as np
out = []
def log(s): print(s, flush=True); out.append(s)
U = 83/85; m = 1/85; W1 = 82/85; k2 = 9.999; EG = math.exp(0.5772156649015329)
def Wf(t):
    if t <= m: return 0.0
    if t <= 1/3: return min(k2 * t * t, t - m)
    if t <= U: return t - m
    return W1
YMAX = 2 * 10**6
sv = np.ones(YMAX + 1, dtype=bool); sv[:2] = False
for p in range(2, int(YMAX ** 0.5) + 1):
    if sv[p]: sv[p*p::p] = False
PR = [int(p) for p in np.nonzero(sv)[0] if 120 % p]          # rho-primes only (rho = 0 kills the others)
PRa = np.array(PR, dtype=float)
INV = np.concatenate([[0.0], np.cumsum(1 / PRa)])             # INV[k] = sum_{j<k} 1/p_j
logV = np.concatenate([[0.0], np.cumsum(np.log1p(-1 / PRa))])
def idx_lt(x): return bisect.bisect_left(PR, x)               # number of rho-primes < x
def V(wv): return math.exp(logV[idx_lt(wv)])                  # V(w) = prod_{p < w, p | rho} (1 - 1/p) (primes 2,3,5 give factor 1)
def sum_inv(a, bnd):                                          # sum of 1/p over rho-primes a <= p < bnd
    i, j = idx_lt(a), idx_lt(bnd)
    return INV[j] - INV[i] if j > i else 0.0

def chain_sum(y, w, constrained, weight_leaf, weight_node=None):
    """sum over squarefree d | P(w) of mu(d) rho(d)/d * F(d), d = p1 > p2 > ... with the prefix condition
    P_{i-1} p_i^3 < y at constrained positions i. Exact enumeration (no aggregation)."""
    tot = 0.0
    def rec(P, last, i, sgn, state):
        nonlocal tot
        tot += sgn / P * weight_leaf(state, i)
        hi = min(last, w)
        k = idx_lt(hi)
        for j in range(k - 1, -1, -1):
            p = PR[j]
            if constrained(i + 1) and P * p**3 >= y: continue
            if P * p > YMAX * 50: continue
            rec(P * p, p, i + 1, -sgn, weight_node(state, p, P, i + 1) if weight_node else state)
    rec(1, float('inf'), 0, 1, None)
    return tot

def Tpm(y, w, plus):
    # enumeration with aggregation of the last unconstrained prime
    tot = 0.0
    con = (lambda i: i % 2 == 1) if plus else (lambda i: i % 2 == 0)
    def rec(P, last, i, sgn):
        nonlocal tot
        tot += sgn / P
        hi = min(last, w)
        nxt = i + 1
        if con(nxt):
            bound = min(hi, (y / P) ** (1/3))
            k = idx_lt(bound)
            for j in range(k - 1, -1, -1):
                rec(P * PR[j], PR[j], nxt, -sgn)
        else:
            # unconstrained: children p with a feasible constrained grandchild need P p q^3 < y for q >= 7
            cut = min(hi, y / (P * 343.0))
            k = idx_lt(cut)
            for j in range(k - 1, -1, -1):
                rec(P * PR[j], PR[j], nxt, -sgn)
            # leaves p in [cut, hi)
            tot += -sgn / P * sum_inv(max(cut, 0), hi) if hi > cut else 0.0
    rec(1, float('inf'), 0, 1)
    return tot

@lru_cache(maxsize=None)
def sigmaP_cached(key):
    eta = key / 1e6
    return Tpm(eta, eta ** (1/3), True)
def sigmaP(eta): return sigmaP_cached(round(eta * 1e6)) if eta < 1e9 else Tpm(eta, eta ** (1/3), True)

def run(y):
    z = y ** U; wy = lambda p: Wf(math.log(p) / math.log(y))
    Vy = V(y)
    # M1: chi with all positions constrained (nu <= 1/m always here)
    M1 = 0.0
    def rec1(P, last, sgn, S):
        nonlocal M1
        M1 += sgn / P * (W1 - S)
        k = idx_lt(min(last, z, (y / P) ** (1/3)))
        for j in range(k - 1, -1, -1):
            p = PR[j]; rec1(P * p, p, -sgn, S + wy(p))
    rec1(1, float('inf'), 1, 0.0)
    # M23: delta = (valid prefix of even length) * last prime p with P p^3 >= y, p < prev, p < z
    M23 = 0.0
    def rec23(P, last, i, S):
        nonlocal M23
        if i % 2 == 0:
            lo = (y / P) ** (1/3); hi = min(last, z)
            for j in range(idx_lt(lo), idx_lt(hi)):
                p = PR[j]
                if P * p**3 < y: continue
                d = P * p
                M23 += (W1 - S - wy(p)) / d * EG * V(math.sqrt(y / d))
        k = idx_lt(min(last, z, (y / P) ** (1/3)))
        for j in range(k - 1, -1, -1):
            p = PR[j]; rec23(P * p, p, i + 1, S + wy(p))
    rec23(1, float('inf'), 0, 0.0)
    # Mstar: chi^- (even positions constrained), weight W1 - sum_i w(p_i) chi*(p_1..p_{i-1}), chi* = odd positions
    Ms = 0.0
    def recS(P, last, i, sgn, Sst, flag):
        nonlocal Ms
        Ms += sgn / P * (W1 - Sst)
        nxt = i + 1; hi = min(last, z)
        if nxt % 2 == 0:
            k = idx_lt(min(hi, (y / P) ** (1/3)))
            for j in range(k - 1, -1, -1):
                p = PR[j]
                recS(P * p, p, nxt, -sgn, Sst + wy(p) * flag, flag)
        else:
            cut = min(hi, y / (P * 343.0)); k = idx_lt(cut)
            for j in range(k - 1, -1, -1):
                p = PR[j]
                recS(P * p, p, nxt, -sgn, Sst + wy(p) * flag, flag and (P * p**3 < y))
            if hi > cut:   # leaves
                for j in range(idx_lt(cut), idx_lt(hi)):
                    p = PR[j]
                    Ms += -sgn / (P * p) * (W1 - Sst - wy(p) * flag)
    recS(1, float('inf'), 0, 1, 0.0, True)
    log(f"y = {y:.0e}: V(y) = {Vy:.5f}; M1 = {M1/Vy:+.4f} V, M23 = {M23/Vy:+.4f} V, M* = {Ms/Vy:+.4f} V")
    log(f"   Lemma 8 (M07): (M1 - M23 - M*)/V(y) = {(M1 - M23 - Ms)/Vy:+.4f}  (pre-asymptotic: equals the Lemma 7 replacement error, see g4_identity.py)")
    # Lemma 9 (M08) for s = 1.5, 2, 3, 4 and both signs
    for s in (1.5, 2.0, 3.0, 4.0):
        for plus in (True, False):
            w = y ** (1 / s)
            T = Tpm(y, w, plus)
            ts = []
            def rect(t, last, nu):
                if (nu % 2 == 0) == plus and (t == 1 or True):
                    ts.append(t)
                lo = y ** (1 / s)
                k = idx_lt(last)
                for j in range(k - 1, -1, -1):
                    p = PR[j]
                    if p <= lo: break
                    if t * p * max(p, t if t > 1 else p) >= y and t > 1:
                        pass
                    tn = t * p
                    qn = max(last if last != float('inf') else 0, p) if t > 1 else p
                    if tn * (qn) < y:
                        rect(tn, p, nu + 1)
            rect(1, float('inf'), 0)
            # condition: all primes > y^{1/s}, largest prime q(t) < y/t, parity; t = 1 included for plus
            tsel = []
            for t in ts:
                tsel.append(t)
            RHS = sum(sigmaP(y / t) / t for t in tsel)
            tag = "  [excluded case: - with s < 2, false as printed]" if (not plus and s < 2) else ""
            log(f"   Lemma 9 (M08) s={s} {'+' if plus else '-'}: T = {T/V(w):+.4f} V(y^(1/s)), t-sum = {RHS/V(w):+.4f}, diff = {(T-RHS)/V(w):+.4f}  ({len(tsel)} t){tag}")
    # Lemma 11 (M10): E11
    Tm = Tpm(y, y ** 0.5, False)
    s1 = 0.0
    for j in range(idx_lt(y ** 0.5), idx_lt(z) + 1):
        if j >= len(PR): break
        p = PR[j]
        if p > z: break
        s1 += (W1 - wy(p)) / p * sigmaP(y / p)
    s2 = 0.0
    for j in range(0, idx_lt(y ** 0.5)):
        p = PR[j]; wp = wy(p)
        if wp == 0: continue
        inner = 0.0
        # n | P(y), even nu(n) >= 2, p < p(n), n p(n) < y/p, chibar_y(n) = 1 (chi(n/p(n)) = 1, chi(n) = 0)
        def recn(P, last, i):
            nonlocal inner
            # try to close with the smallest prime q (position i+1, i+1 even): need chi(P)=1 (ensured), P q^3 >= y, n q < y/p
            if (i + 1) % 2 == 0:
                lo = max(p + 1, (y / P) ** (1/3))
                hi = min(last, math.sqrt(y / (p * P)))
                for jj in range(idx_lt(lo), idx_lt(hi)):
                    q = PR[jj]
                    if q <= p or P * q**3 < y: continue
                    n = P * q
                    if n * q < y / p:
                        inner += 1.0 / n * sigmaP(y / (p * n))
            k = idx_lt(min(last, (y / P) ** (1/3)))
            for jj in range(k - 1, -1, -1):
                q = PR[jj]
                if q <= p: break
                recn(P * q, q, i + 1)
        recn(1, float('inf'), 0)
        s2 += wp / p * (sigmaP(y / p) - inner)
    E11 = W1 * Tm - s1 + s2
    log(f"   Lemma 11 (M10): E11 = {E11/Vy:+.4f} V, (M* - E11)/V = {(Ms - E11)/Vy:+.4f}")
    log(f"   Lemma 12 (M11): E11/(2 e^gamma V(y)) = {E11/(2*EG*Vy):+.4f} (limit mvalW ~ 0.0105); Lemma 6: (M1 - M23)/(2 e^gamma V) = {(M1-M23)/(2*EG*Vy):+.4f}")
for y in [10**4, 10**5, 10**6]:
    run(float(y))
open(sys.argv[1], 'w').write("\n".join(out) + "\n")
