"""Brute-force test of Greaves 1986 Lemma 10 (p. 93) as transcribed for ItemM09.
b(n) = sum_{d | n, q(n/d) < y/(p n)} mu(d) chi_y(d); claim b(1) = 1 and for n > 1:
b(n) = -chibar_y(n) if n p(n) < y/p, else 0.  Tested over squarefree n with all prime factors > p,
for several m, strict and non-strict variants of the conditions."""
import math, random, itertools, sys
sys.path.insert(0, '.')
from greaves_comb import chi, chibar, mu, pf, divisors, minfac, primesLt
def qmax(n): return pf(n)[-1] if n > 1 else 1
def bfun(y, m, p, n, strict):
    s = 0
    for d in divisors(n):
        q = qmax(n // d); lim = y / (p * n)
        if (q < lim) if strict else (q <= lim): s += mu(d) * chi(y, m, d)
    return s
res = {}
import sys as _s
KS = [0, 2, 4] if 'even' in _s.argv else [0, 1, 2, 3, 4]
rnd = random.Random(3)
for strict in (True, False):
    for cond_strict in (True, False):
        bad = tot = 0; ex = None
        for trial in range(400):
            y = rnd.uniform(100, 20000); m = rnd.choice([0.05, 0.1, 0.2, 0.34, 1/85])
            ps = primesLt(60)
            p = rnd.choice(ps[:6])
            big = [q for q in ps if q > p]
            k = rnd.choice(KS)
            n = math.prod(rnd.sample(big, k)) if k <= len(big) else 1
            lhs = bfun(y, m, p, n, strict)
            if n == 1: rhs = 1
            else:
                c = (n * minfac(n) < y / p) if cond_strict else (n * minfac(n) <= y / p)
                rhs = -chibar(y, m, n) if c else 0
            tot += 1
            if lhs != rhs:
                bad += 1
                if ex is None: ex = (y, m, p, n, lhs, rhs)
        print(f"b(n) with q(n/d) {'<' if strict else '<='} y/(pn), case n p(n) {'<' if cond_strict else '<='} y/p: {tot} cases, {bad} mismatches, first {ex}")
