"""Exact check of the M* transcription (Greaves (4.9)) against Greaves' derivation (4.10):
M*(z) = M1(z) - sum_{delta in D} chibar(delta) rho(delta) phi(delta)/delta * T+(y/delta, p(delta)),
i.e. Lemma 8 with the Lemma 7 replacement e^gamma V(sqrt(y/delta)) -> T+(y/delta, p(delta)) made exactly.
Also: the Lemma 8 discrepancy at finite y comes from that replacement for small y/delta."""
import sys, math
sys.argv = [sys.argv[0], '/dev/null']
exec(open('g4_check.py').read().split("for y in [10**4")[0])
out2 = []
def run2(y):
    z = y ** U; wy = lambda p: Wf(math.log(p) / math.log(y)); Vy = V(y)
    M1 = 0.0
    def rec1(P, last, sgn, S):
        nonlocal M1
        M1 += sgn / P * (W1 - S)
        k = idx_lt(min(last, z, (y / P) ** (1/3)))
        for j in range(k - 1, -1, -1):
            p = PR[j]; rec1(P * p, p, -sgn, S + wy(p))
    rec1(1, float('inf'), 1, 0.0)
    M23T = 0.0; M23 = 0.0
    def rec23(P, last, i, S):
        nonlocal M23T, M23
        if i % 2 == 0:
            lo = (y / P) ** (1/3); hi = min(last, z)
            for j in range(idx_lt(lo), idx_lt(hi)):
                p = PR[j]
                if P * p**3 < y: continue
                d = P * p
                M23T += (W1 - S - wy(p)) / d * Tpm(y / d, p, True)
                M23 += (W1 - S - wy(p)) / d * EG * V(math.sqrt(y / d))
        k = idx_lt(min(last, z, (y / P) ** (1/3)))
        for j in range(k - 1, -1, -1):
            p = PR[j]; rec23(P * p, p, i + 1, S + wy(p))
    rec23(1, float('inf'), 0, 0.0)
    Ms = 0.0
    def recS(P, last, i, sgn, Sst, flag):
        nonlocal Ms
        Ms += sgn / P * (W1 - Sst)
        nxt = i + 1; hi = min(last, z)
        if nxt % 2 == 0:
            k = idx_lt(min(hi, (y / P) ** (1/3)))
            for j in range(k - 1, -1, -1):
                p = PR[j]; recS(P * p, p, nxt, -sgn, Sst + wy(p) * flag, flag)
        else:
            k = idx_lt(hi)
            for j in range(k - 1, -1, -1):
                p = PR[j]; recS(P * p, p, nxt, -sgn, Sst + wy(p) * flag, flag and (P * p**3 < y))
    recS(1, float('inf'), 0, 1, 0.0, True)
    log(f"y = {y:.0e}: M* (4.9) = {Ms/Vy:+.6f} V; M1 - M23T (4.10) = {(M1 - M23T)/Vy:+.6f} V; difference {(Ms - M1 + M23T)/Vy:+.2e} V; Lemma 8 replacement error (M23T - M23)/V = {(M23T - M23)/Vy:+.4f}")
for y in (3000.0, 10**4, 3 * 10**4):
    run2(float(y))
