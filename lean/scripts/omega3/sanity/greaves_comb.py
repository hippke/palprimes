"""Sanity checks of the Greaves 1986 combinatorial items (S01 Lemma 1, S02 Lemma 2, S03, S04, S13 coefficient
identity) on small integers with random weights. Definitions mirror Omega3/DefsSieve.lean literally."""
import random, math, sys, itertools
from fractions import Fraction
from sympy import factorint, primerange, divisors, isprime

def pf(n): return sorted(factorint(n).keys()) if n > 1 else []
def omega(n): return len(pf(n))
def minfac(n): return pf(n)[0] if n > 1 else 1
def mu(n):
    f = factorint(n)
    if any(e > 1 for e in f.values()): return 0
    return (-1) ** len(f)
def sqfree(n): return mu(n) != 0
def radLt(a, z): return math.prod(p for p in pf(a) if p < z)
def Ssv(a, z): return 1 if all(p >= z for p in pf(a)) else 0
def LamA(n, c, w):
    if n == 1: return c
    if isprime(n): return w(n)
    return 0
def phiW(w, W1, d): return W1 - sum(w(p) for p in pf(d))
def chiJR(y, m, d):
    for h in divisors(d):
        if h == 1: continue
        k = omega(h)
        if k % 2 == 0 or k <= 1 / m:
            if not (h * minfac(h) ** 2 < y): return False
    return True
def chi(y, m, d): return 1 if chiJR(y, m, d) else 0
def chibar(y, m, d): return 0 if d == 1 else chi(y, m, d // minfac(d)) - chi(y, m, d)
def primesLt(z): return [p for p in primerange(2, math.ceil(z) + 1) if p < z]

def SigmaG(y, z, W1, w, a):
    a = radLt(a, z)
    lam = LamA(radLt(a, z), W1, w)
    l2 = 0
    for p1 in primesLt(z):
        if a % p1: continue
        for p2 in primesLt(p1):
            if a % p2 or not (y <= p2 * p2 * p1): continue
            r = a // (p1 * p2)
            l2 += (W1 - w(p1)) * Ssv(r, p2) - w(p2) * Ssv(r, p1)
    return lam - l2
def inner(y, z, W1, w, a, d):
    return sum(mu(t) * phiW(w, W1, t * d) for t in divisors(radLt(a, minfac(d))))
def Sig1(y, z, W1, w, m, a): return sum(mu(d) * chi(y, m, d) * phiW(w, W1, d) for d in divisors(radLt(a, z)))
def Sig2(y, z, W1, w, m, a):
    s = 0
    for p in pf(radLt(a, z)):
        br = phiW(w, W1, p) * Ssv(a // p, math.sqrt(y / p))
        for q in pf(a // p):
            if q < p and q * q * p < y: br += w(q) * Ssv(a // (p * q), p)
        s += -chibar(y, m, p) * br
    return s
def Sig3(y, z, W1, w, m, a):
    return sum(mu(d) * chibar(y, m, d) * inner(y, z, W1, w, a, d) for d in divisors(radLt(a, z))
               if omega(d) % 2 == 1 and omega(d) >= 3 and omega(d) <= 1 / m)
def Sig4(y, z, W1, w, m, a):
    return sum(mu(d) * chibar(y, m, d) * inner(y, z, W1, w, a, d) for d in divisors(radLt(a, z))
               if omega(d) % 2 == 0 and omega(d) >= 2)


def nu(a, Y):
    f = factorint(a)
    return sum(1 for p in f if p < Y) + sum(e for p, e in f.items() if p >= Y)

def make_w(y, U, V, rnd):
    tab = {}
    def w(p):
        if p not in tab:
            t = math.log(p) / math.log(y)
            if t >= U: tab[p] = U - V
            elif t <= V: tab[p] = 0.0
            else:
                cap = (t - V) if t >= 1/3 else (t - max(V, (1 - U) / 2))
                tab[p] = max(0.0, cap) * rnd.choice([1.0, rnd.random()])
        return tab[p]
    return w

if __name__ == '__main__':
    rnd = random.Random(7)
    cnt = {"L2": [0, 0], "L1": [0, 0], "S03": [0, 0], "S04": [0, 0]}
    for trial in range(300):
        y = rnd.uniform(50, 5000); U = rnd.uniform(0.55, 0.99); V = (1 - U) / 2 * rnd.choice([1, 0.5, 0]); m = max(V, (1 - U) / 2)
        W1 = U - V
        z = y ** U * rnd.choice([1, 1.3, 2])
        w = make_w(y, U, V, rnd)
        g = V + 3 * U
        for _ in range(12):
            primes = primesLt(min(z, 80)) or [2]
            a = 1
            for _ in range(rnd.randint(0, 6)): a *= rnd.choice(primes)
            if rnd.random() < 0.4: a *= rnd.choice([1, 101, 103, 107, 109, 9973])
            if a < 2 or a >= y ** g: continue
            A = radLt(a, z)
            # S02 for squarefree A | P(z)
            lhs = SigmaG(y, z, W1, w, A)
            rhs = Sig1(y, z, W1, w, m, A) + Sig2(y, z, W1, w, m, A) + Sig3(y, z, W1, w, m, A) + Sig4(y, z, W1, w, m, A)
            cnt["L2"][0] += 1; cnt["L2"][1] += abs(lhs - rhs) > 1e-9
            # S01 Lemma 1 (radical form)
            tgt = w(minfac(a)) if nu(a, y ** U) <= 3 else 0.0
            cnt["L1"][0] += 1
            if SigmaG(y, z, W1, w, a) > tgt + 1e-12:
                cnt["L1"][1] += 1
                if cnt["L1"][1] <= 3: print("L1 viol", y, U, V, z, a, factorint(a), SigmaG(y, z, W1, w, a), tgt)
            # S03 Sigma4 >= 0 (holds under Lemma 4(iii) for these w)
            s4 = Sig4(y, z, W1, w, m, A)
            cnt["S03"][0] += 1; cnt["S03"][1] += s4 < -1e-12
            # S04 Sigma2+Sigma3 >= - sum_{delta in D, delta | A} LamA((A/delta, P(sqrt(y/delta))), phi(delta), w)
            bound = 0.0
            for d in divisors(A):
                if d == 1 or omega(d) % 2 == 0 or omega(d) > 1 / m or chibar(y, m, d) != 1: continue
                bound += LamA(radLt(A // d, math.sqrt(y / d)), phiW(w, W1, d), w)
            s23 = Sig2(y, z, W1, w, m, A) + Sig3(y, z, W1, w, m, A)
            cnt["S04"][0] += 1
            if s23 < -bound - 1e-12:
                cnt["S04"][1] += 1
                if cnt["S04"][1] <= 3: print("S04 viol", y, U, V, a, s23, -bound)
    for k, (n, b) in cnt.items(): print(f"{k}: {n} cases, {b} violations")

def SigmaG_literal(y, z, W1, w, a):
    """Greaves (2.14) at a itself (not at (a, P(z))): used only to reproduce the finding of NOTES §3.1."""
    lam = LamA(radLt(a, z), W1, w)
    l2 = 0
    for p1 in primesLt(z):
        if a % p1: continue
        for p2 in primesLt(p1):
            if a % p2 or not (y <= p2 * p2 * p1): continue
            r = a // (p1 * p2)
            l2 += (W1 - w(p1)) * Ssv(r, p2) - w(p2) * Ssv(r, p1)
    return lam - l2

if __name__ == '__main__' and 'literal' in sys.argv:
    random.seed(1)
    bad = badsq = tot = 0
    for trial in range(400):
        y = random.uniform(30, 3000); z = random.uniform(2, y); m = random.choice([0.05, 0.1, 0.2, 1/85, 0.3])
        W1 = random.uniform(0.3, 1); wtab = {}
        def w(p):
            if p not in wtab: wtab[p] = Fraction(random.randint(0, 100), 97)
            return wtab[p]
        for _ in range(15):
            primes = primesLt(min(z, 60)) or [2]
            a = 1
            for _ in range(random.randint(0, 5)): a *= random.choice(primes)
            if random.random() < 0.3: a *= random.choice([1, 101, 103, 107])
            lhs = SigmaG_literal(y, z, W1, w, a)
            rhs = Sig1(y, z, W1, w, m, a) + Sig2(y, z, W1, w, m, a) + Sig3(y, z, W1, w, m, a) + Sig4(y, z, W1, w, m, a)
            tot += 1
            if abs(float(lhs - rhs)) > 1e-9:
                bad += 1; badsq += sqfree(a)
    print(f"Lemma 2 (2.23) with Greaves' Sigma at a itself (literal): {tot} cases, {bad} mismatches, {badsq} of them with squarefree a")
