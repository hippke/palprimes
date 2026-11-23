"""Numerical controls for the lemmas of the paper (not part of the proofs).

(1) Lemma 3.1, injectivity. All nonzero u in [-H, H]^B give W_u = sum_b u_b r^(l b + 1) != 0 and |W_u| < r^(lB+1).
    Control with H = r^l, where zeros must occur.
(2) Lemma 3.1, identity sum_{h mod d} prod_b T(r^(lb+1) h/d) = d tau_0^B + d R(d) for random tau >= 0.
(3) The majorant (1 - p) + p cos^2(pi t) >= |cos(pi t)|^(2p) of Proposition 4.1(a).
(4) Proposition 4.1(a) and Proposition 4.3 for small r and M.
(5) Lemma 4.5 (pointwise bound) exhaustively for small moduli.
(6) The large-sieve step of Proposition 4.4 (Lemma 4.2 bound for sum F); the full bound of Proposition 4.4 is tested in prop_h_test.py.
(7) Sanity scan of S(D)/D, S(D) = sum_{d in [D,2D), (d,r)=1} sum*_h F(h/d).
(8) Lebesgue means int_0^1 K_l^p (upper limit of block rates, Remark 9.2).
"""
import itertools, math, random
import numpy as np
from math import gcd, comb

random.seed(146)


def W_u(u, r, l):
    return sum(ub * r ** (l * b + 1) for b, ub in enumerate(u))


def F_at(r, M, h, d):
    """F(h/d) = prod_{1<=j<=M} |cos(pi r^j h/d)| for integer arrays h, d (exact reduction mod d)."""
    out = np.ones(len(h))
    for j in range(1, M + 1):
        out *= np.abs(np.cos(np.pi * ((pow(r, j) * h) % d) / d))
    return out


def reduced(D, r):
    P = [(h, d) for d in range(D, 2 * D) if gcd(d, r) == 1 for h in range(1, d) if gcd(h, d) == 1]
    P = np.array(P, dtype=np.int64)
    return P[:, 0], P[:, 1]


print("== (1) Lemma 3.1, injectivity")
for (r, l, B) in [(3, 1, 6), (3, 2, 3), (4, 1, 5), (4, 2, 3), (5, 1, 4), (3, 3, 2), (2, 1, 8), (2, 3, 2)]:
    H = r ** l - 1
    bad = 0; mx = 0; n = 0
    for u in itertools.product(range(-H, H + 1), repeat=B):
        if not any(u):
            continue
        w = W_u(u, r, l); n += 1
        bad += (w == 0); mx = max(mx, abs(w))
    print(f"r={r} l={l} B={B} H={H}: {n} vectors, zeros={bad}, max|W_u|={mx} < r^(lB+1)={r ** (l * B + 1)}: {mx < r ** (l * B + 1)}")
r, l, B = 3, 1, 3; H = r ** l
z = sum(1 for u in itertools.product(range(-H, H + 1), repeat=B) if any(u) and W_u(u, r, l) == 0)
print(f"control H = r^l (r=3, l=1, B=3): zeros={z} (must be > 0)")
r = 3; E = [j for j in range(1, 13) if j % 2 == 0]
z = sum(1 for u in itertools.product((-1, 0, 1), repeat=len(E)) if any(u) and sum(a * r ** j for a, j in zip(u, E)) == 0)
print(f"even positions r=3, E={E}, H=1: zeros={z}")

print("== (2) identity of Lemma 3.1")
mx = 0
for (r, l, B) in [(3, 1, 4), (3, 2, 2), (4, 1, 3), (5, 1, 3), (3, 1, 5)]:
    H = r ** l - 1
    for d in [2, 5, 7, 8, 10, 11, 13, 16, 25, 31]:
        tau = [random.random() for _ in range(H + 1)]
        T = lambda x: tau[0] + 2 * sum(tau[u] * math.cos(2 * math.pi * u * x) for u in range(1, H + 1))
        lhs = sum(math.prod(T((r ** (l * b + 1) * h % d) / d) for b in range(B)) for h in range(d))
        Rd = sum(math.prod(tau[abs(x)] for x in u) for u in itertools.product(range(-H, H + 1), repeat=B)
                 if any(u) and W_u(u, r, l) % d == 0)
        rhs = d * tau[0] ** B + d * Rd
        mx = max(mx, abs(lhs - rhs) / max(1, abs(rhs)))
print(f"identity: 50 cases (d coprime and not coprime to r), max relative error {mx:.2e}")

print("== (3) majorant (1-p) + p cos^2 >= |cos|^(2p)")
t = np.linspace(0, 0.5, 200001)
worst = min(((1 - p) + p * np.cos(np.pi * t) ** 2 - np.abs(np.cos(np.pi * t)) ** (2 * p)).min()
            for p in [0.1, 0.5, 0.9, 0.99, 0.999, 1.0])
print(f"min gap over grid and p in {{0.1,...,1}}: {worst:.3e} (>= 0 up to rounding)")

print("== (4) Proposition 4.1(a) (W(a)) and Proposition 4.3 (L)")
for (r, M) in [(3, 14), (4, 12), (5, 10), (7, 9)]:
    for D in [8, 30, 100]:
        P = np.array([(h, d) for d in range(D, 2 * D) if gcd(d, r) == 1 for h in range(d)], dtype=np.int64)
        F = F_at(r, M, P[:, 0], P[:, 1])
        for p in [0.5, 0.9]:
            lhs = (F ** p).sum(); main = 2 * D * D * (1 - p / 2) ** ((M - 1) / 2)
            print(f"W(a) r={r} M={M} D={D} p={p}: sum F^p = {lhs:.4g}, 2D^2(1-p/2)^((M-1)/2) = {main:.4g}, "
                  f"ratio to main + 2D: {lhs / (main + 2 * D):.3f}")
        h, d = reduced(D, r)
        FR = F_at(r, M, h, d)
        m = min(M, int(math.floor(math.log(D * D, r))))
        for k in range(1, min(r, 4)):
            m2k = comb(2 * k, k) / 4 ** k
            lhs = (FR ** (2 * k)).sum(); rhs = (r ** (m + 1) + 4 * D * D) * m2k ** m
            print(f"   L r={r} D={D} k={k} m={m}: sum F^2k = {lhs:.4g} <= {rhs:.4g}: {lhs <= rhs}")

print("== (5) Lemma 4.5, F(h/d) <= cos(pi/(2r))^floor(M/K), K = ceil(log_r d), all reduced h/d, 2 <= d <= 300")
for (r, M) in [(3, 30), (4, 24), (5, 20), (10, 16)]:
    worst = 0.0
    for d in range(2, 301):
        if gcd(d, r) != 1:
            continue
        K = 1
        while r ** K < d:
            K += 1
        h = np.array([x for x in range(1, d) if gcd(x, d) == 1], dtype=np.int64)
        F = F_at(r, M, h, np.full(len(h), d))
        worst = max(worst, (F / math.cos(math.pi / (2 * r)) ** (M // K)).max())
    print(f"r={r} M={M}: max of F / bound = {worst:.4f} (must be <= 1)")

print("== (6) large-sieve step of Proposition 4.4: sum over reduced h/q, q in [Q,2Q), of F <= (r^L + 4Q^2) m_2k^L, 2kL <= M")
for (r, M, k) in [(3, 24, 1), (3, 24, 2), (4, 20, 2), (5, 18, 2), (7, 16, 3)]:
    m2k = comb(2 * k, k) / 4 ** k
    for Q in [4, 16, 64]:
        h, d = reduced(Q, r)
        lhs = F_at(r, M, h, d).sum()
        L = int(math.floor(math.log(4 * Q * Q, r)))
        if 2 * k * L > M:
            continue
        rhs = (r ** L + 4 * Q * Q) * m2k ** L
        print(f"r={r} M={M} k={k} Q={Q} L={L}: sum F = {lhs:.4g} <= {rhs:.4g}: {lhs <= rhs}")
print("S_2k(r) = sup_u sum_c cos^2k(pi (u+c)/r) equals r m_2k for k <= r-1 (grid in u):")
for (r, k) in [(3, 1), (3, 2), (4, 2), (4, 3), (6, 3), (10, 5)]:
    u = np.linspace(0, 1, 20001)
    S = sum(np.cos(np.pi * (u + c) / r) ** (2 * k) for c in range(r))
    print(f"   r={r} k={k}: max {S.max():.12f}, min {S.min():.12f}, r m_2k = {r * comb(2 * k, k) / 4 ** k:.12f}")

print("== (7) sanity scan S(D)/D (small for D below |W|^(1/2), linear growth beyond)")
for (r, M) in [(3, 22), (4, 18), (5, 16), (8, 14)]:
    Wn = 2 ** M
    line = []
    for D in [2 ** k for k in range(3, 13)]:
        if D > 16 * Wn ** 0.5:
            break
        tot = 0.0
        for d in range(D, 2 * D):
            if gcd(d, r) != 1:
                continue
            hh = np.array([x for x in range(1, d) if gcd(x, d) == 1], dtype=np.int64)
            F = np.ones(len(hh))
            for j in range(1, M + 1):
                F *= np.abs(np.cos(np.pi * ((pow(r, j, d) * hh) % d) / d))
            tot += F.sum()
        line.append(f"D={D}:{tot / D:.3g}")
    print(f"r={r} M={M} |W|^(1/2)={Wn ** 0.5:.0f}: " + " ".join(line))

print("== (8) -log_r(int_0^1 K_l^p)/l, p = 0.99 (upper limit for blocks of length l), midpoint rule")
for r in (3, 4):
    for l in range(1, 6):
        n = min(400000 * r ** (l - 1), 20_000_000)
        t = (np.arange(n) + 0.5) / n
        K = np.ones(n)
        for i in range(l):
            K *= np.abs(np.cos(np.pi * r ** i * t))
        I = (K ** 0.99).mean()
        print(f"r={r} l={l}: int K^0.99 = {I:.6f}, rate per digit {-math.log(I) / math.log(r) / l:.5f}")
    print(f"r={r}: log_r(pi/2) = {math.log(math.pi / 2) / math.log(r):.5f}, lambda/2 = {math.log(2) / (2 * math.log(r)):.5f}")
