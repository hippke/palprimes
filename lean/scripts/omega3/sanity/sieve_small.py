"""Brute-force sanity checks of the exact sieve items S06, S09 (exact part), S11 (support), S12, S13 and M01 on small
parameters. The Lean definitions fix (U, m) = (83/85, 1/85); the identities S12, M01 and the support statements hold for
any (U, m, w), so they are tested here with small z = y^U (U = 0.5..0.6) to make P(z) enumerable, random weights w,
a toy band structure, and the density of base b = 5 (r = 120). Definitions mirror Omega3/DefsSieve.lean."""
import sys, math, random, itertools
from fractions import Fraction
sys.path.insert(0, '.')
from greaves_comb import (pf, omega, minfac, mu, sqfree, radLt, LamA, phiW, chi, chibar, primesLt, Sig1, divisors)
from math import gcd
out = []
def log(s): print(s); out.append(s)
b = 5; r = b**3 - b
def rhoB(d): return 1 if gcd(d, r) == 1 else 0
def ltSet(z): return [n for n in range(1, math.ceil(z) + 1) if n < z]
def totient(n):
    res = n
    for p in pf(n): res = res // p * (p - 1)
    return res
def gS(n): return 1 / totient(n) if sqfree(n) and gcd(n, r) == 1 else 0.0
def GS(z): return sum(gS(n) for n in ltSet(z))
def eval_step(s, u):
    acc = 0.0
    for (a, v) in s:
        if a <= u: acc = v
    return acc
def lamA_vec(e, x):
    z = math.sqrt(x); G = GS(z); L = ltSet(z)
    def etaQ(q): return eval_step(e, math.log(q) / math.log(z)) / G
    def etaK(k): return sum(etaQ(q) for q in pf(k))
    nu = (1 + sum(gS(k) * etaK(k) for k in L)) / G
    yk = {k: mu(k) * gS(k) * (nu - etaK(k)) for k in L}
    lam = {}
    for d in L:
        if gcd(d, r) == 1:
            lam[d] = d * sum(mu(k // d) * yk[k] for k in L if k % d == 0)
    return lam   # zero elsewhere
def chiProp_list(y, m, d): return chi(y, m, d) == 1
rng = random.Random(11)
s12_bad = m01_bad = s11_bad = s13_bad = s09_bad = s06_bad = tot = 0
for trial in range(25):
    y = rng.uniform(150, 900); U = rng.uniform(0.45, 0.6); m = rng.choice([0.2, 0.34, 0.12]); eps = rng.uniform(0, 1)
    z = y ** U; W1 = rng.uniform(0.5, 1)
    wtab = {}
    def w(p):
        if p not in wtab: wtab[p] = rng.random() * 0.3
        return wtab[p]
    Pz = math.prod(primesLt(z))
    D = [d for d in divisors(Pz) if d != 1 and chibar(y, m, d) == 1 and omega(d) % 2 == 1 and omega(d) <= 1 / m]
    # toy bands: two step functions, edges in exponent of p
    etas = [[(0.1, 0.05), (0.4, -0.02)], [(0.2, 0.03)]]
    xs = [1/3, 0.4, 0.5]
    def etaOf(d):
        if len(pf(d)) == 1 and pf(d)[0] == d:
            x = math.log(d) / math.log(y)
            for i in range(2):
                if xs[i] <= x < xs[i + 1]: return etas[i]
        return []
    LAM = {d: lamA_vec(etaOf(d), y / d) for d in D}
    def LamD(d, k): return LAM[d].get(k, 0.0)
    def c(n):
        first = mu(n) * chi(y, m, n) * phiW(w, W1, n) if Pz % n == 0 else 0.0
        s = 0.0
        for d in D:
            if n % d: continue
            L = ltSet(math.sqrt(y / d))
            s += phiW(w, W1, d) * sum(LamD(d, d1) * LamD(d, d2) for d1 in L for d2 in L if (d1 * d2 // gcd(d1, d2)) * d == n)
        return first - (1 + eps) * s
    # S13
    cD = 0.5 * (2/3) ** (1 / m)   # (1/2)(2/3)^{1/m - 1}-type bound; Lean uses (1/2)(2/3)^84 with 1/m = 85
    for d in D:
        s13_ok = y <= d * minfac(d) ** 2 and y / d >= y ** (0.5 * (2/3) ** (math.floor(1/m) - 1)) and sqfree(d)
        s13_bad += not s13_ok
    # S09 exact part: lambda_1 = 1, support
    for d in D:
        lam = LAM[d]; xx = y / d
        if abs(lam.get(1, 0) - 1) > 1e-9: s09_bad += 1
        for k, v in lam.items():
            if abs(v) > 1e-12 and not (sqfree(k) and k < math.sqrt(xx)): s09_bad += 1
    # S11 support over all n | P(z)
    cvals = {}
    for n in divisors(Pz):
        cv = c(n); cvals[n] = cv
        if abs(cv) > 1e-12 and not (sqfree(n) and n <= y): s11_bad += 1
    # M01
    MTs = sum(cvals[n] * rhoB(n) / n for n in divisors(Pz))
    M1 = sum(mu(d) * chi(y, m, d) * phiW(w, W1, d) * rhoB(d) / d for d in divisors(Pz))
    def Q(d):
        L = ltSet(math.sqrt(y / d))
        return sum(LamD(d, d1) * LamD(d, d2) * rhoB(d1 * d2 // gcd(d1, d2)) / (d1 * d2 // gcd(d1, d2)) for d1 in L for d2 in L)
    rhs = M1 - (1 + eps) * sum(phiW(w, W1, d) * rhoB(d) / d * Q(d) for d in D)
    m01_bad += abs(MTs - rhs) > 1e-9 * max(1, abs(rhs))
    # S12 for random a
    for _ in range(20):
        primes = primesLt(z)
        a = 1
        for _ in range(rng.randint(0, 6)): a *= rng.choice(primes)
        a *= rng.choice([1, 1, 1009, 1013])
        A = radLt(a, z)
        lhs = sum(cvals.get(n, None) if n in cvals else c(n) for n in divisors(a))
        rhs = Sig1(y, z, W1, w, m, A) - (1 + eps) * sum(phiW(w, W1, d) * sum(LamD(d, k) for k in divisors(A // d)) ** 2 for d in D if A % d == 0)
        tot += 1; s12_bad += abs(lhs - rhs) > 1e-9 * max(1, abs(rhs))
log(f"S12 expansion identity: {tot} random a over 25 random (y, U, m, eps, w), {s12_bad} mismatches")
log(f"M01 main-term identity: 25 cases, {m01_bad} mismatches")
log(f"S11 support (c(n) != 0 => squarefree, n <= y; n | P(z) by construction): {s11_bad} violations")
log(f"S13 facts on D (y <= delta p(delta)^2, y/delta >= y^((1/2)(2/3)^(floor(1/m)-1)), squarefree): {s13_bad} violations")
log(f"S09 exact part (lambda_1 = 1, support squarefree d < sqrt x): {s09_bad} violations")
# S06 generic Lemma 3 pointwise
bad = 0
for trial in range(3000):
    z1 = rng.uniform(2, 40); cc = rng.uniform(0, 2); K = rng.uniform(1, 2)
    L = [d for d in range(1, math.ceil(z1)) if d < z1 and sqfree(d)]
    lam = {d: (1.0 if d == 1 else rng.uniform(-1, 1)) for d in L}
    def f(q):
        if q not in lam: return rng.uniform(-1, 5)
        return K * cc * (1 + lam[q]) ** 2 * rng.uniform(0, 1)
    M = rng.randint(1, 5000)
    A = radLt(M, z1)
    lhs = LamA(A, cc, f)
    rhs = K * cc * sum(lam.get(d, 0.0) for d in divisors(M)) ** 2
    bad += lhs > rhs + 1e-9
log(f"S06 Lemma 3 pointwise (generic): 3000 random cases, {bad} violations")
open(sys.argv[1], 'w').write("\n".join(out) + "\n")
