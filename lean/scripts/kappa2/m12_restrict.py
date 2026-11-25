#!/usr/bin/env python3
"""M12 at R = 2: restrict the Omega3 h-table (cells xi_j = (101/100)^j/85, bounds HbQ_j, independent of theta, U)
to [2/103, 1/4] and evaluate MvalLower for the new weight W (m = 2/103, kSq = 582/103, U = 99/103).

New table: xi'_0 = 2/103, xi'_i = xiQ(J0 + i) (1 <= i < n), xi'_n = 1/4, Hb'_i = HbQ(J0 + i), with J0 = 50,
n = 308 - J0 (old cell J0 = [xiQ(J0), xiQ(J0+1)] contains [2/103, xiQ(J0+1)]).
Cell integral bound IQ(a, b) = min((b - a)(1 - m/b), kSq (b^2 - a^2)/2) >= int_a^b W/t (W <= t - m, W <= kSq t^2).
Prints the base part (exact closed form, mpmath), the exact rational cell sum, and MvalLower >= base - sum.
Positive control: the Omega3 constants (m = 1/85, kSq = 9999/1000, U = 83/85, J0 = 0) reproduce base 0.0321844
and sum <= 23/1000 of OK2/Omega3 M12."""
import re, sys
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 40
LIT = '/astro/palindromic-primes/omega-2/lean/OK2/Items/M12_Lit.lean'
src = open(LIT).read()
h2 = [int(x) for x in re.search(r'def h2Lit : List ℕ := \[([^\]]*)\]', src).group(1).split(',')]
rest = [int(x) for x in re.search(r'def restLit : List ℕ := \[([^\]]*)\]', src).group(1).split(',')]
TT = 2 ** 64
tau = sum(F(4) ** (2 * (9 + k)) / F(__import__('math').factorial(2 * (9 + k))) for k in range(33))


def xiQ(j): return F(101 ** j, 85 * 100 ** j)


def getD(l, i): return l[i] if i < len(l) else 0


def HbQ(j): return F(getD(h2, j) + getD(rest, j // 2), TT) + F(85 * 100 ** j, 101 ** j) * tau


def run(m, k2, U, W1, J0, head):
    n = 308 - J0
    assert xiQ(J0) <= head and (J0 == 0 or head < xiQ(J0 + 1))
    xs = [head] + [xiQ(J0 + i) for i in range(1, n)] + [F(1, 4)]
    hb = [HbQ(J0 + i) for i in range(n)]

    def IQ(a, b): return min((b - a) * (1 - m / b), k2 * (b * b - a * a) / 2)
    S = sum(hb[i] * IQ(xs[i], xs[i + 1]) for i in range(n))
    # base: -int_{1/2}^1 (W1 - W)/((1-t)t) + int_0^{1/2} W/((1-t)t)
    mm_, kk, UU = mp.mpf(m.numerator) / m.denominator, mp.mpf(k2.numerator) / k2.denominator, mp.mpf(U.numerator) / U.denominator
    W1m = mp.mpf(W1.numerator) / W1.denominator

    def W(t):
        if t <= mm_: return mp.mpf(0)
        if t <= mp.mpf(1) / 3: return min(kk * t * t, t - mm_)
        if t <= UU: return t - mm_
        return W1m
    disc = mp.sqrt(1 - 4 * kk * mm_)
    t1, t2 = (1 - disc) / (2 * kk), (1 + disc) / (2 * kk)
    pts = sorted(set([mp.mpf(0), mm_, t1, t2, mp.mpf(1) / 3, mp.mpf(1) / 2]))
    pts = [p for p in pts if p <= mp.mpf(1) / 2]
    I2 = sum(mp.quad(lambda t: W(t) / ((1 - t) * t), [pts[i], pts[i + 1]]) for i in range(len(pts) - 1) if pts[i + 1] > mm_)
    I1 = mp.quad(lambda t: (W1m - W(t)) / ((1 - t) * t), [mp.mpf(1) / 2, UU]) + 0
    base = -I1 + I2
    return dict(n=n, t1=t1, t2=t2, base=base, S=S, Sf=float(S), low=base - mp.mpf(S.numerator) / S.denominator)


if __name__ == '__main__':
    old = run(F(1, 85), F(9999, 1000), F(83, 85), F(82, 85), 0, F(1, 85))
    print('control Omega3: base %.7f  sum %.7f  (<= 0.023: %s)  low %.7f' % (old['base'], old['Sf'], old['S'] <= F(23, 1000), old['low']))
    new = run(F(2, 103), F(582, 103), F(99, 103), F(97, 103), 50, F(2, 103))
    print('R=2: n %d cells, kinks t1 %.6f t2 %.6f' % (new['n'], new['t1'], new['t2']))
    print('R=2: base %.7f  sum %.7f  MvalLower >= %.7f' % (new['base'], new['Sf'], new['low']))
    print('R=2: sum <= 17/1000: %s' % (new['S'] <= F(17, 1000)))
    try:
        run(F(2, 103), F(582, 103), F(99, 103), F(97, 103), 51, F(2, 103))
        print('negative control FAILED: head outside cell accepted')
    except AssertionError:
        print('negative control: head 2/103 outside cell [xi_51, xi_52] rejected')
