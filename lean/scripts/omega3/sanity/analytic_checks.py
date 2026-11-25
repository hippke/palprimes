"""Sanity checks of the continuous-parameter sieve items: S05 / S07 (admissibility of the weight of the route, Lemma 4
(i) above x_n, (ii') for odd nu >= 3, (3.10), Lemma 4 (iii)), BandOK's x_n condition, M03 (G(sqrt x) e^gamma V(sqrt x) -> 1),
and the value of mvalW / MvalLower (M12, M13) from the h cells of lean/omega3_p0/mainterm (Q = 2000 two-sided cells)."""
import sys, math, random
import numpy as np
out = []
def log(s): print(s); out.append(s)
U = 83/85; m = 1/85; V = m; W1 = 82/85; k2 = 9.999
def W(t):
    if t <= m: return 0.0
    if t <= 1/3: return min(k2 * t * t, t - m)
    if t <= U: return t - m
    return W1
xn = 0.625103127                      # r188 cert_add x_n at theta = 0.340 (5 bands)
log(f"BandOK x_n condition: k^2(1-xn)^2 = {k2*(1-xn)**2:.6f} <= 4(U-xn) = {4*(U-xn):.6f}: {k2*(1-xn)**2 <= 4*(U-xn)}; xn <= 2U-1 = {2*U-1:.6f}: {xn <= 2*U-1}")
# (a) nu = 1, x in [xn, 1): W(t) <= phi (2t/(1-x))^2 for m < t < (1-x)/2
worst = (1e9, None)
for x in np.linspace(xn, 0.9999, 4000):
    phi = W1 - W(x)
    if (1 - x) / 2 * 0.9999999 <= m * 1.0000001: continue   # no admissible t (then W(t) = 0 for 2t < 1 - x)
    ts = np.linspace(m * 1.0000001, (1 - x) / 2 * 0.9999999, 400)
    for t in ts:
        v = phi * (2 * t / (1 - x)) ** 2 - W(t)
        if v < worst[0]: worst = (v, (x, t, W(t)))
worst, wloc = worst
log(f"S07 (nu = 1, x >= x_n): min of phi(2t/(1-x))^2 - W(t) over 1.6M grid points: {worst:.3e} at (x, t, W) = {wloc}")
# exact rational recheck at the worst point region: x near U, t near m (relative rounding)
from fractions import Fraction as Fr
Ue, me = Fr(83, 85), Fr(1, 85)
def We(t):
    if t <= me: return Fr(0)
    if t <= Fr(1, 3): return min(Fr(9999, 1000) * t * t, t - me)
    if t <= Ue: return t - me
    return Ue - me
xw, tw = Fr(wloc[0]), Fr(wloc[1])
phie = (Ue - me) - We(xw)
log(f"   exact rational value at that grid point: {float(phie * (2 * tw / (1 - xw)) ** 2 - We(tw)):.3e}")
# control: below x_n with plain Selberg weights the condition fails somewhere (that is why bands are needed)
worst_c = 1e9
for x in np.linspace(1/3, xn, 400):
    phi = W1 - W(x)
    for t in np.linspace(m * 1.0000001, (1 - x) / 2 * 0.9999999, 400):
        worst_c = min(worst_c, phi * (2 * t / (1 - x)) ** 2 - W(t))
log(f"   control x in [1/3, x_n): min {worst_c:.3e} (negative expected: bands needed)")
# (b) odd nu >= 3, sampled admissible tuples (exponent form of (3.15))
rng = random.Random(3)
bad_ii = bad_310 = tot = 0; worst_ii = 1e9
def admissible_prefix(xs):
    s = 0.0
    for i, xi in enumerate(xs):
        if not (3 * xi + s < 1): return False
        s += xi
    return True
for trial in range(200000):
    nu = rng.choice([3, 3, 3, 5, 5, 7, 9])
    xs = []
    ok = True
    for i in range(nu - 1):
        hi = (1 - sum(xs)) / 3
        if xs: hi = min(hi, xs[-1])
        if hi <= m: ok = False; break
        xs.append(rng.uniform(max(m, hi * rng.uniform(0.3, 1.0)), hi))
    if not ok or not admissible_prefix(xs): continue
    lo = (1 - sum(xs)) / 3
    if lo >= xs[-1]: continue
    xs.append(rng.uniform(lo, xs[-1]))
    X = sum(xs)
    if X >= 1: continue
    phi = W1 - sum(W(xi) for xi in xs)
    tmax = min(xs[-1], (1 - X) / 2)
    for _ in range(5):
        t = rng.uniform(0, tmax)
        tot += 1
        val = phi * (2 * t / (1 - X)) ** 2 - W(t)
        worst_ii = min(worst_ii, val); bad_ii += val < -1e-12
        bad_310 += W(t) > phi + 1e-12
log(f"S07 (odd nu >= 3, Lemma 4 (ii')): {tot} sampled (tuple, t), {bad_ii} violations, min slack {worst_ii:.3e}; (3.10) violations {bad_310}")
# (c) Lemma 4 (iii): even nu >= 2 with chibar = 1: sum W(x_i) <= W(1)
bad = tot = 0; worst = 1e9
for trial in range(200000):
    nu = rng.choice([2, 2, 4, 4, 6])
    xs = []; ok = True
    for i in range(nu - 1):
        hi = (1 - sum(xs)) / 3
        if xs: hi = min(hi, xs[-1])
        if hi <= 0: ok = False; break
        xs.append(rng.uniform(hi * rng.uniform(0.0, 1.0), hi))
    if not ok or not admissible_prefix(xs): continue
    lo = (1 - sum(xs)) / 3
    if lo >= xs[-1]: continue
    xs.append(rng.uniform(lo, xs[-1]))
    tot += 1; s = sum(W(x) for x in xs); worst = min(worst, W1 - s); bad += s > W1 + 1e-12
log(f"S05 Lemma 4 (iii): {tot} sampled even tuples, {bad} violations, min slack {worst:.3e}")
# M03: G(sqrt x) e^gamma V(sqrt x) -> 1 for b = 5 (r = 120)
r = 120
def ratio(wmax):
    N = int(wmax)
    sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if sieve[p]: sieve[p*p::p] = False
    primes = np.nonzero(sieve)[0]
    phi = np.arange(N + 1, dtype=float); sqf = np.ones(N + 1, dtype=bool)
    for p in primes:
        phi[p::p] *= (1 - 1 / p)
        sqf[p*p::p*p] = False
    n = np.arange(N + 1)
    cop = (n % 2 != 0) & (n % 3 != 0) & (n % 5 != 0)
    sel = sqf & cop; sel[0] = False
    res = []
    for wv in (10**3, 10**4, 10**5, 10**6, N):
        G = (1 / phi[1:wv][sel[1:wv]]).sum()
        Vv = np.prod([1 - 1 / p for p in primes[primes < wv] if r % p])
        res.append((wv, G * math.exp(0.5772156649015329) * Vv))
    return res
log("M03 G(w) e^gamma V(w) for w = 1e3, 1e4, 1e5, 1e6, 4e6 (b = 5): " + ", ".join(f"{v:.5f}" for _, v in ratio(4 * 10**6)))
# mvalW from the Q = 2000 h cells (r170/r182 two-sided enclosures, cells from xi0 = 0.0112)
d = np.load('/astro/palindromic-primes/lean/omega3_p0/mainterm/logs/hcells_x112_Q2000.npz')
xi0 = float(d['xi0']); Q = float(d['Q']); hup = d['h_up']; hlo = d['h_lo']
edges = xi0 * (1 + 1 / Q) ** np.arange(len(hup) + 1)
def integ(f, a, bb, n=20001):
    t = np.linspace(a, bb, n); y = np.array([f(s) for s in t]); return np.trapezoid(y, t)
A = -integ(lambda t: (W1 - W(t)) / ((1 - t) * t), 0.5, U) + integ(lambda t: W(t) / ((1 - t) * t), m, 0.5, 200001)
Hup = Hlo = 0.0
for j in range(len(hup)):
    a, bb = edges[j], min(edges[j + 1], 0.5)
    if a >= 0.5: break
    if bb <= m: continue
    a = max(a, m)
    I = integ(lambda t: W(t) / t, a, bb, 21)
    Hup += hup[j] * I; Hlo += hlo[j] * I
log(f"M12/M13 mvalW: 𝓜(W) in [{A - Hup:.6f}, {A - Hlo:.6f}] (trapezoid, Q = 2000 h cells; target >= 0.0098; r188 M_low 0.010484 with k = 3.16227)")
log(f"   h(t,1) cell upper bounds: max {hup.max():.4f}, h = 0 beyond t = {edges[np.nonzero(hup > 0)[0].max() + 1]:.4f}")
open(sys.argv[1], 'w').write("\n".join(out) + "\n")
