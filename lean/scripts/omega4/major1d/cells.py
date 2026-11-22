"""Exact cell certificates for T(c) >= psi(c)^q on c in [-1,1] (c = cos 2 pi t), bases 4..9.
Mirrors the Lean checker in Palprimes/Major1D/Cheb.lean exactly (Fractions)."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import json, sys, math
from fractions import Fraction as Fr

FIN = os.path.join(HERE, '..', 'majorants') + os.sep
FILES = {4: 'maj1d_b4_H3_p49_50.json', 5: 'maj1d_b5_H4_p47_50.json', 6: 'maj1d_b6_H5_p23_25.json',
         7: 'maj1d_b7_H6_p9_10.json', 8: 'maj1d_b8_H7_p22_25.json', 9: 'maj1d_b9_H8_p22_25.json'}

def padd(P, Q):
    n = max(len(P), len(Q)); P = P + [Fr(0)] * (n - len(P)); Q = Q + [Fr(0)] * (n - len(Q))
    return [a + b for a, b in zip(P, Q)]
def psmul(s, P): return [s * a for a in P]
def cheb(k):
    T0, T1 = [Fr(1)], [Fr(0), Fr(1)]
    if k == 0: return T0
    for _ in range(k - 1):
        T0, T1 = T1, padd(psmul(Fr(-1), T0), [Fr(0)] + psmul(Fr(2), T1))
    return T1
def shift(L, m):
    if not L: return []
    S = shift(L[1:], m)
    return padd(padd([L[0]], psmul(m, S)), [Fr(0)] + S)
def absb(L, h):
    r = Fr(0)
    for a in reversed(L): r = abs(a) + h * r
    return r
def lowbd(L, h):
    if not L: return Fr(0)
    return L[0] - h * absb(L[1:], h)
def peval(L, x):
    r = 0
    for a in reversed(L): r = a + x * r
    return r

def load(b):
    d = json.load(open(FIN + FILES[b]))
    p = Fr(d['p']); c = d['c']
    PT = psmul(Fr(c[0], 2**52), cheb(0))
    for k in range(1, len(c)): PT = padd(PT, psmul(Fr(2 * c[k], 2**52), cheb(k)))
    Ppsi = psmul(Fr(1, b), cheb(0))
    for k in range(1, b): Ppsi = padd(Ppsi, psmul(Fr(2 * (b - k), b * b), cheb(k)))
    return d, p, c, PT, Ppsi

def rup(x, bits=40):  # rational >= x (float x, with safety handled by exact check)
    return Fr(math.ceil(x * 2**bits), 2**bits)

def cell_ok(PT, Ppsi, q, lo, hi, w, A, B):
    nq, dq = q.numerator, q.denominator
    if not (w > 0 and A >= (1 - q) * w**nq and B * w**(dq - nq) >= q and lo < hi): return False
    F = padd(PT, psmul(-B, Ppsi)); F[0] -= A
    m, h = (lo + hi) / 2, (hi - lo) / 2
    return lowbd(shift(F, m), h) >= 0

def choose(PT, Ppsi, q, lo, hi):
    nq, dq = q.numerator, q.denominator
    m = (lo + hi) / 2
    cands = []
    for x in [m, lo, hi]:
        u0 = float(peval(Ppsi, x))
        if u0 > 1e-12: cands.append(u0)
    us = [float(peval(Ppsi, lo + (hi - lo) * Fr(i, 8))) for i in range(9)]
    cands.append(max(us) + 1e-9)
    for u0 in cands:
        wf = u0 ** (1.0 / dq)
        w = Fr(round(wf * 2**24), 2**24)
        if w <= 0: continue
        A = rup(float((1 - q) * Fr(w)**nq) * (1 + 1e-12) + 1e-15)
        B = rup(float(q / Fr(w)**(dq - nq)) * (1 + 1e-12) + 1e-15)
        # fix exactly
        while A < (1 - q) * w**nq: A += Fr(1, 2**40)
        while B * w**(dq - nq) < q: B += Fr(1, 2**40)
        if cell_ok(PT, Ppsi, q, lo, hi, w, A, B): return (w, A, B)
    return None

def run(b, n0=8, maxdepth=30):
    d, p, c, PT, Ppsi = load(b)
    q = p / 2
    cells = []
    stack = [(Fr(-1) + Fr(2 * i, n0), Fr(-1) + Fr(2 * (i + 1), n0)) for i in range(n0)][::-1]
    while stack:
        lo, hi = stack.pop()
        r = choose(PT, Ppsi, q, lo, hi)
        if r is None:
            if hi - lo < Fr(1, 2**maxdepth): raise RuntimeError(f'fail at {lo},{hi}')
            mid = (lo + hi) / 2
            stack.append((mid, hi)); stack.append((lo, mid))
        else:
            cells.append((lo, hi) + r)
    return d, p, PT, Ppsi, cells

if __name__ == '__main__':
    for b in range(4, 10):
        d, p, PT, Ppsi, cells = run(b)
        print(b, p, 'cells', len(cells), 'min width', float(min(c[1]-c[0] for c in cells)))
