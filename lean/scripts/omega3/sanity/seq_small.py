"""Brute-force sanity checks of the level/square items on small cases (L08, L09, L12, L13, L14, L17, Q01, Q02, Q03).
Definitions mirror Omega3/Defs.lean literally (cK, palVal, wDig, aW, AW, XW, RW, fg, gJ, mw4, trigEval, trigMass,
redRes, FareyW, levelSum, L1farey). Floats with tolerance 1e-9 relative."""
import sys, math, itertools, random
import numpy as np
from math import gcd
from sympy import primerange, factorint, divisors, isprime
sys.path.insert(0, sys.argv[2] if len(sys.argv) > 2 else '.')
from level_records import recG
out = []
def log(s): print(s); out.append(s)
def cK(b, N, k): return b**k + b**(2*N - k) if k < N else b**N
def bigB(b): return b**3 - b
def omega(n): return len(factorint(n)) if n > 1 else 0
def sqfree(n): return n >= 1 and all(e == 1 for e in factorint(n).values())
def e(t): return np.exp(2j * np.pi * t)
def Gg(b, g, t): return sum(g[a] * e(a * t) for a in range(b))
def fg(b, g, N, al): return np.prod([Gg(b, g, cK(b, N, k) * al) for k in range(N + 1)])
def gJ(b, g, N, J, al): return np.prod([Gg(b, g, cK(b, N, k) * al) for k in J])
def mw4(b, g): return sum(sum(g[i] * g[s - i] for i in range(s + 1) if i < b and s - i < b) ** 2 for s in range(2 * b - 1))
def redRes(q): return [h for h in range(q) if gcd(h, q) == 1]
def digvecs(b, N): return itertools.product(range(b), repeat=N + 1)
def palVal(b, N, d): return sum(d[k] * cK(b, N, k) for k in range(N + 1))
def wDig(g, d): return math.prod(g[x] for x in d)
def seqdata(b, g, N):
    r = bigB(b); aw = {}
    for d in digvecs(b, N):
        n = palVal(b, N, d)
        if gcd(n, r) == 1: aw[n] = aw.get(n, 0) + wDig(g, d)
    return aw
def AW(aw, q): return sum(v for n, v in aw.items() if n % q == 0)
TOL = 1e-9
# L17
for b, N in ((5, 2), (6, 2), (8, 1), (7, 2)):
    g = [float(recG(b, a)) for a in range(b)]
    aw = seqdata(b, g, N); X = AW(aw, 1)
    ok = all(v <= (1/3) ** (N + 1) + 1e-15 for v in aw.values())
    ok &= all(b**(2*N) <= n < b**(2*N+1) and str(np.base_repr(n, b)) == str(np.base_repr(n, b))[::-1] for n in aw)
    ok &= X <= 1 + 1e-12
    log(f"L17 b={b} N={N}: a_n <= 3^-(N+1), support in piStar, X_w={X:.6f} <= 1: {ok}")
# L13 X_w by DP modulo r (exact distribution of n mod r)
for b in (5, 6, 7, 8, 9, 12):
    g = [float(recG(b, a)) for a in range(b)]; r = bigB(b)
    vals = []
    for N in (4, 8, 12, 16, 17, 24, 25):
        dist = np.zeros(r); dist[0] = 1.0
        for k in range(N + 1):
            c = cK(b, N, k) % r; new = np.zeros(r)
            for a in range(b):
                if g[a]: new += g[a] * np.roll(dist, (a * c) % r)
            dist = new
        vals.append(sum(dist[i] for i in range(r) if gcd(i, r) == 1))
    log(f"L13 b={b}: X_w for N=4,8,12,16,17,24,25: " + ", ".join(f"{v:.6f}" for v in vals))
# Q03 Parseval mod p^2 (exact identity)
mx = 0; cnt = 0
for b, N in ((5, 4), (6, 3), (8, 3), (7, 3)):
    g = [float(recG(b, a)) for a in range(b)]; m4 = mw4(b, g)
    for j in range(1, N):
        for p in primerange(2, 400):
            if b % p == 0 or p * p < 2 * b ** (2 * j + 1) or p * p > 30000: continue
            beta = random.random(); J = range(N - j, N)
            lhs = sum(abs(gJ(b, g, N, J, h / p**2 + beta)) ** 4 for h in range(p * p))
            rhs = p * p * m4 ** j
            mx = max(mx, abs(lhs / rhs - 1)); cnt += 1
log(f"Q03 E' identity: {cnt} cases (b in 5..8, j < N, p^2 >= 2b^(2j+1)), max |ratio-1| = {mx:.2e}")
# Q03 control: fails when p^2 < 2 b^(2j+1)
b, N, j = 5, 4, 2; g = [float(recG(b, a)) for a in range(b)]; m4 = mw4(b, g)
p = 23; lhs = sum(abs(gJ(b, g, N, range(N - j, N), h / p**2 + 0.3)) ** 4 for h in range(p * p)); log(f"   control b=5 j=2 p=23 (p^2=529 < 2*5^5=6250): ratio {lhs/(p*p*m4**j):.4f} (need not be 1)")
# Q01 reduction inequality
viol = 0; cnt = 0
for b, N in ((5, 3), (6, 2), (8, 2)):
    g = [float(recG(b, a)) for a in range(b)]; r = bigB(b); aw = seqdata(b, g, N); X = AW(aw, 1)
    tau = len(divisors(r))
    for p in primerange(2, 60):
        A = AW(aw, p * p)
        rhs = tau * sum(p**-2 * (sum(abs(fg(b, g, N, h / p**2 + k / r)) for h in range(p * p) if h % p) +
                                 sum(abs(fg(b, g, N, h / p + k / r)) for h in range(1, p))) for k in range(r))
        cnt += 1; viol += abs(A - X / p**2) > rhs * (1 + TOL) + 1e-12
log(f"Q01 reduction: {cnt} cases (all primes < 60, including p | r), {viol} violations")
# Q02 T_K over square / prime moduli
viol = 0; cnt = 0
rng = random.Random(5)
for trial in range(40):
    b = rng.choice([5, 6, 7]); N = rng.choice([3, 4]); H = rng.randint(0, 2 * b - 2)
    tau = [rng.random() for _ in range(H + 1)]
    K = [k for k in range(1, N) if rng.random() < 0.7]; Q = rng.randint(2, 12); beta = rng.random()
    T = lambda t: tau[0] + 2 * sum(tau[u] * math.cos(2 * math.pi * u * t) for u in range(1, H + 1))
    TK = lambda al: math.prod(T(cK(b, N, k) * al) for k in K)
    mass = abs(tau[0]) + 2 * sum(abs(t) for t in tau[1:])
    ell = math.log(2 * H * b ** (2 * N + 1)) / math.log(Q) if H > 0 else 0.0
    ps = [p for p in primerange(Q, 2 * Q)]
    l1 = sum(TK(h / p**2 + beta) for p in ps for h in range(p * p)); r1 = 4 * Q**3 * tau[0] ** len(K) + 4 * Q**2 * ell * mass ** len(K)
    l2 = sum(TK(h / p + beta) for p in ps for h in range(p)); r2 = 4 * Q**2 * tau[0] ** len(K) + 2 * Q * ell * mass ** len(K)
    cnt += 2; viol += (l1 > r1 * (1 + TOL)) + (l2 > r2 * (1 + TOL))
log(f"Q02 diagonal bounds: {cnt} random cases (tau >= 0), {viol} violations")
# L08 Lemma 2.8 with Td = number of moduli (trivial valid bound) and with the exact max count
viol = 0; cnt = 0; tight = 0
for trial in range(60):
    b = rng.choice([3, 5, 6]); N = rng.choice([2, 3, 4]); H = rng.randint(0, 2 * b - 2)
    tau = [rng.uniform(-0.3, 1) for _ in range(H + 1)]
    K = [k for k in range(N) if rng.random() < 0.7]
    Qs = rng.sample(range(1, 40), rng.randint(1, 6)); beta = rng.random()
    T = lambda t: tau[0] + 2 * sum(tau[u] * math.cos(2 * math.pi * u * t) for u in range(1, H + 1))
    lhs = sum(math.prod(T(cK(b, N, k) * (h / q + beta)) for k in K) for q in Qs for h in range(q))
    mass = abs(tau[0]) + 2 * sum(abs(t) for t in tau[1:])
    Td = len(Qs)
    rhs = sum(Qs) * tau[0] ** len(K) + max(Qs) * Td * mass ** len(K)
    cnt += 1; viol += lhs > rhs + 1e-9 * max(1, abs(rhs))
log(f"L08 Lemma 2.8: {cnt} random cases (signed tau, H <= 2b-2), {viol} violations")
# L09 Lemma 2.9_w
viol = 0; cnt = 0; worst = 0
for b, N in ((5, 3), (6, 3), (8, 2), (7, 3)):
    g = [float(recG(b, a)) for a in range(b)]; m4 = mw4(b, g)
    for j in range(1, N + 1):
        for D in (1, 2, 3, 5, 8, 13, 30):
            beta = rng.random(); J = range(N - j, N)
            lhs = sum(abs(gJ(b, g, N, J, h / d + beta)) ** 4 for d in range(D, 2 * D) if gcd(d, b) == 1 for h in redRes(d))
            rhs = (4 * D * D + 2 * b * b ** (2 * j)) * m4 ** j
            cnt += 1; viol += lhs > rhs * (1 + TOL); worst = max(worst, lhs / rhs)
log(f"L09 Lemma 2.9_w: {cnt} cases, {viol} violations, max lhs/rhs {worst:.3f}")
# L12 Lemma K
viol = 0; cnt = 0; worst = 0
for trial in range(3000):
    b = rng.choice([5, 6, 7, 8, 10]); g = [float(recG(b, a)) for a in range(b)]; r = bigB(b)
    N = rng.randint(4, 16); M = rng.randint(2, N - 1)
    q = rng.randint(2, 3000)
    if gcd(q, r) != 1: continue
    h = rng.randint(1, q - 1)
    if gcd(h, q) != 1: continue
    k = rng.randint(0, r - 1); al = h / q + k / r
    prod = math.prod(abs(Gg(b, g, cK(b, N, n) * al)) for n in range(1, M + 1))
    Lq = max(1, int(math.floor(math.log(q, b) + 1e-12)))
    while b ** Lq > q: Lq -= 1
    while b ** (Lq + 1) <= q: Lq += 1
    Lq = max(1, Lq)
    bound = math.exp(-(g[0] * g[1]) * ((M - 1) // Lq) / (b**4 * (b + 1) ** 2))
    cnt += 1; viol += prod > bound * (1 + 1e-12); worst = max(worst, prod / bound)
log(f"L12 Lemma K: {cnt} random points, {viol} violations, max product/bound {worst:.4f}")
# L14 regrouping
viol = 0; cnt = 0
for b, N in ((5, 2), (5, 3), (6, 2)):
    g = [float(recG(b, a)) for a in range(b)]; r = bigB(b); aw = seqdata(b, g, N); X = AW(aw, 1)
    tau = len(divisors(r))
    for D in (5, 20, 60):
        lev = sum(3 ** omega(d) * abs(AW(aw, d) - X * (1 if gcd(d, r) == 1 else 0) / d) for d in range(1, D + 1) if sqfree(d))
        def Farey(beta): return sum(3 ** omega(q) / q * sum(abs(fg(b, g, N, h / q + beta)) for h in redRes(q)) for q in range(2, D + 1) if gcd(q, r) == 1)
        Kt = max(Farey(k / r) for k in range(r))
        H = sum(3 ** omega(e_) / e_ for e_ in range(1, D + 1))
        cnt += 1; viol += lev > tau * H * Kt * (1 + TOL)
log(f"L14 regrouping: {cnt} cases, {viol} violations")
open(sys.argv[1], 'w').write("\n".join(out) + "\n")
