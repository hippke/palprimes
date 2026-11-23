"""Numerical tests of Proposition 4.4 (Hoelder over blocks + large sieve), Lemma 4.2, Lemma 4.5,
and the frequency-distinctness condition k <= r-1. Written by an independent checker, lightly cleaned.
S(D) = sum over reduced h/d, D <= d < 2D, d >= 2, (d,r)=1, of F(h/d), F = prod_{j=1}^M |cos(pi r^j h/d)|.
Claim: if 2k floor(log_r(4D^2)) <= M then S(D) <= 8 m_{2k}^{-1} D^{1-c_k}, c_k = 2 psi_{2k} - 1.
"""
import math
import numpy as np
from math import comb, gcd

def farey(D, r):
    hs, ds = [], []
    for d in range(max(D, 2), 2 * D):
        if gcd(d, r) != 1:
            continue
        h = np.arange(1, d)
        h = h[np.gcd(h, d) == 1]
        hs.append(h); ds.append(np.full(h.size, d))
    if not hs: return np.zeros(0, np.int64), np.zeros(0, np.int64)
    return np.concatenate(hs), np.concatenate(ds)

def G(h, d, r, a, L, k2=1.0):
    """prod_{a<=j<a+L} |cos(pi r^j h/d)| computed exactly mod d (integer residues)."""
    out = np.ones(h.size)
    cur = h.astype(np.int64) % d
    for _ in range(a):
        cur = (cur * r) % d          # exact residue of h r^a mod d
    for j in range(L):
        out *= np.abs(np.cos(np.pi * cur / d))
        cur = (cur * r) % d
    return out

def logr(x, r): return math.log(x) / math.log(r)

print("== Proposition 4.4: S(D) vs 8 m^{-1} D^{1-c_k}, with M = 2kL (tightest) ")
worst = 0
for (r, k) in [(3, 1), (3, 2), (4, 2), (4, 3), (5, 2), (5, 4), (6, 3), (7, 3), (10, 4)]:
    m = comb(2 * k, k) / 4 ** k
    if not r * m * m < 1:
        print(f"r={r} k={k}: r m^2 = {r*m*m:.3f} >= 1, skipped"); continue
    psi = -logr(m, r); c = 2 * psi - 1
    for e in range(1, 10):
        D = 2 ** e
        L = int(math.floor(logr(4 * D * D, r) + 1e-12))
        while r ** (L + 1) <= 4 * D * D: L += 1
        while r ** L > 4 * D * D: L -= 1
        M = 2 * k * L
        h, d = farey(D, r)
        if h.size > 3_000_000: break
        if h.size == 0: continue
        F = G(h, d, r, 1, M)
        S = F.sum()
        bound = 8 / m * D ** (1 - c)
        # Hoelder factors: sum_x G_{0,L}(r^{1+iL} x)^{2k} for i < 2k, all equal to sum_x G_{0,L}(x)^{2k}
        base = (G(h, d, r, 0, L) ** (2 * k)).sum()
        facs = [(G(h, d, r, 1 + i * L, L) ** (2 * k)).sum() for i in range(2 * k)]
        perm_err = max(abs(f - base) / base for f in facs)
        holder = np.prod([f ** (1 / (2 * k)) for f in facs])
        ls = (r ** L + 4 * D * D) * m ** L
        ok = S <= holder * (1 + 1e-12) and base <= ls and holder <= bound * (1 + 1e-12)
        worst = max(worst, S / bound)
        print(f"r={r} k={k} c_k={c:.4f} D={D:4d} L={L:2d} M={M:3d} #pts={h.size:8d} S={S:.4e} "
              f"Hoelder={holder:.4e} LSfac={ls:.4e} bound={bound:.4e} S/bound={S/bound:.3e} "
              f"perm_rel_err={perm_err:.1e} ok={ok}")
print(f"max S/bound over all cases: {worst:.3e} (must be <= 1)")

print("\n== Lemma 4.2 needs k <= r-1: int_0^1 G_{0,L}^{2k} (= sum |c_n|^2 by Parseval) vs m_{2k}^L")
for (r, k, L) in [(3, 1, 3), (3, 2, 3), (3, 3, 2), (3, 4, 2), (4, 3, 2), (4, 4, 2), (5, 4, 2), (5, 5, 2)]:
    N = 2 ** 20
    t = (np.arange(N) + 0.5) / N
    g = np.ones(N)
    for j in range(L):
        g *= np.abs(np.cos(np.pi * r ** j * t))
    I = (g ** (2 * k)).mean()
    m = comb(2 * k, k) / 4 ** k
    print(f"r={r} k={k} L={L}: int G^2k = {I:.10f}, m^L = {m**L:.10f}, equal={abs(I-m**L)<1e-9}  (k<=r-1: {k<=r-1})")

print("\n== Lemma 4.5 pointwise: max over reduced h/d, 2<=d<=D0, (d,r)=1 of F(h/d)/cos(pi/(2r))^floor(M/K)")
for (r, M, D0) in [(3, 30, 3000), (4, 24, 3000), (5, 20, 3000), (7, 18, 2000), (10, 16, 2000), (3, 7, 3000)]:
    worst = 0; arg = None
    for d in range(2, D0 + 1):
        if gcd(d, r) != 1: continue
        K = 1
        while r ** K < d: K += 1
        h = np.arange(1, d); h = h[np.gcd(h, d) == 1]
        F = G(h, np.full(h.size, d), r, 1, M)
        b = math.cos(math.pi / (2 * r)) ** (M // K)
        q = F.max() / b
        if q > worst: worst = q; arg = (d, int(h[F.argmax()]))
    print(f"r={r} M={M} d<={D0}: max ratio {worst:.4f} at h/d = {arg[1]}/{arg[0]} (must be <= 1)")
