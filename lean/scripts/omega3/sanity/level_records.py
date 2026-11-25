"""Sanity checks of the record data and the level-side numeric items (L01, L03, L04, L05, L06, L07, L16).
Definitions mirror Omega3/Defs.lean (recG, recP, recH, fejTau, recTau, trigEval, trigMass, mw4).
Run with python3 -I; exact rationals where the item is exact, floats (grid) where it is a pointwise inequality."""
import sys, math
from fractions import Fraction as F
import numpy as np
import mpmath as mp
mp.mp.dps = 60

def fejerW(m, a):
    return F(min(a + 1, 2 * m - 1 - a), m * m) if a + 1 < 2 * m else F(0)
def mB(b): return (b + 1) // 2
g6 = [F(9,100),F(17,100),F(24,100),F(24,100),F(17,100),F(9,100)]
g8 = [F(x,5242880) for x in [336527,627976,867075,1052006,920934,736003,496904,205455]]
P6 = [F(1321873323313001,4503599627370496),F(7222560589874485,36028797018963968),F(8214455710924505,72057594037927936),F(2794269570583501,72057594037927936)]
P8 = [F(8383891917856039,36028797018963968),F(1576219461424283,9007199254740992),F(4168387876891915,36028797018963968),F(4833877587123735,72057594037927936),F(3409766388037827,144115188075855872),F(5108764914694413,2305843009213693952)]
def recG(b, a):
    if b == 6: return g6[a] if a < 6 else F(0)
    if b == 8: return g8[a] if a < 8 else F(0)
    return fejerW(mB(b), a)
def recP(b): return F(1023,1024) if b <= 15 else 1 - F(1, b*b)
def recH(b): return 3 if b == 6 else 5 if b == 8 else mB(b) - 1
def fejTau(m, u):
    if u == 0: return F(1, m)
    return F(m - u, m * m) if u < m else F(0)
def recPoly(b, u):
    if b == 6: return P6[u] if u < len(P6) else F(0)
    if b == 8: return P8[u] if u < len(P8) else F(0)
    return fejTau(mB(b), u)
def recTau(b, u): return (1 - recP(b) if u == 0 else 0) + recP(b) * recPoly(b, u)
def trigMass(b): return abs(recTau(b, 0)) + 2 * sum(abs(recTau(b, u)) for u in range(1, recH(b) + 1))
def mw4(b):
    g = [recG(b, a) for a in range(b)]
    return sum(sum(g[i] * g[s - i] for i in range(s + 1) if i < b and s - i < b) ** 2 for s in range(2 * b - 1))
def Gabs(b, t):
    g = np.array([float(recG(b, a)) for a in range(b)])
    a = np.arange(b)
    return np.abs(np.exp(2j * np.pi * np.outer(t, a)) @ g)
def trig(H, tau, t):
    return float(tau[0]) + 2 * sum(float(tau[u]) * np.cos(2 * np.pi * u * t) for u in range(1, H + 1))

out = []
def log(s): print(s); out.append(s)

# L16 record facts
bad = 0
for b in range(5, 401):
    g = [recG(b, a) for a in range(b)]
    ok = sum(g) == 1 and all(x >= 0 for x in g) and g[0] > 0 and g[1] > 0 and max(g) <= F(1, 3) and 0 < recP(b) < 1 and recH(b) <= 2 * b - 2
    bad += not ok
log(f"L16 record facts b=5..400: {bad} failures")

# L01 Fejer identity |G| = F_m (float)
rng = np.random.default_rng(1)
mx = 0
for m in range(1, 25):
    t = rng.uniform(-3, 3, 400)
    a = np.arange(2 * m - 1)
    g = np.array([float(fejerW(m, x)) for x in a])
    G = np.abs(np.exp(2j * np.pi * np.outer(t, a)) @ g)
    k = np.arange(-m + 1, m)
    Fm = (1 / m) * ((1 - np.abs(k) / m)[None, :] * np.cos(2 * np.pi * np.outer(t, k))).sum(1)
    mx = max(mx, np.abs(G - Fm).max())
log(f"L01 |G_fejer| - F_m, m=1..24, 400 random y each: max abs diff {mx:.2e}")

# L03 closed form (exact)
bad = 0
for m in range(1, 41):
    lhs = sum(sum(fejerW(m, i) * fejerW(m, s - i) for i in range(s + 1)) ** 2 for s in range(4 * m))
    rhs = F(151 * m**6 + 70 * m**4 + 49 * m**2 + 45, 315 * m**7)
    bad += lhs != rhs
log(f"L03 Fejer fourth moment closed form m=1..40: {bad} mismatches")

# L04, L05 exact LP majorants (float grid)
for b, P in ((6, P6), (8, P8)):
    t = np.linspace(0, 0.5, 400001)
    d = trig(len(P) - 1, P, t) - Gabs(b, t)
    log(f"L0{4 if b == 6 else 5} P_{b} - |G_g{b}| on 400001 grid points of [0,1/2]: min {d.min():.3e} at t={t[d.argmin()]:.6f}; P(0)-1 = {float(P[0] + 2*sum(P[1:]) - 1):.3e}")

# L06 record majorant T >= |G|^p (float grid), b = 5..120
worst = (1, None)
for b in range(5, 121):
    t = np.linspace(0, 0.5, 20001)
    tau = [recTau(b, u) for u in range(recH(b) + 1)]
    d = trig(recH(b), tau, t) - Gabs(b, t) ** float(recP(b))
    if d.min() < worst[0]: worst = (d.min(), b)
log(f"L06 T - |G|^p on 20001 grid points, b=5..120: min {worst[0]:.3e} (b={worst[1]}) [>= -1e-12 expected: Fejer T - |G|^p vanishes where F = 1]")

# L07 record numerics: best psi, theta_w, kappa with exact power checks in mpmath
thS, th0, c1 = mp.mpf(17)/50, mp.mpf(3)/10, mp.mpf(83)/250
rows = []; fails = []
for b in list(range(5, 301)) + [500, 1000, 10**4, 10**5]:
    tau0 = recTau(b, 0); mass = trigMass(b); m4 = mw4(b) if b <= 300 else None
    p = recP(b)
    psi = -mp.log(mp.mpf(tau0.numerator) / tau0.denominator) / mp.log(b)
    lA = mp.log(mp.mpf(mass.numerator) / mass.denominator) / mp.log(b)
    if m4 is None:  # Fejer closed form for large b
        m = mB(b); m4 = F(151*m**6 + 70*m**4 + 49*m**2 + 45, 315*m**7)
    thw = -mp.log(mp.mpf(m4.numerator) / m4.denominator) / mp.log(b) - 1
    q = 1 - mp.mpf(p.numerator) / p.denominator
    # kappa range: (ii*) 2θ+2κ < ψ + q(2θθw-2κ)/3 ; (iii*) lA+2κ < q(2θ0θw-2κ)/3
    k2 = (psi + q * 2 * thS * thw / 3 - 2 * thS) / (2 + 2 * q / 3)
    k3 = (q * 2 * th0 * thw / 3 - lA) / (2 + 2 * q / 3)
    kmax = min(k2, k3)
    Q1 = psi - 2 * c1
    Q2 = q * psi * thw - 3 * lA
    rows.append((b, float(psi), float(lA), float(thw), float(kmax), float(k2), float(k3), float(Q1), float(Q2)))
    if not (kmax > 0 and thw > 0 and Q1 > 0 and Q2 > 0): fails.append(b)
log(f"L07 record numerics b=5..300 and 500, 1000, 1e4, 1e5: failures {fails}")
mins = {}
for name, idx in (("kappa_max", 4), ("(ii) kappa bound", 5), ("(iii) kappa bound", 6), ("Q1 slack psi-2c1", 7), ("Q2' slack", 8), ("theta_w", 3)):
    r = min(rows, key=lambda r: r[idx]); mins[name] = r
    log(f"   min {name}: {r[idx]:.4e} at b={r[0]} (psi={r[1]:.6f}, lA={r[2]:.2e}, theta_w={r[3]:.5f})")
for b in (5, 6, 7, 8, 9, 10, 15, 16, 17, 30, 100, 300):
    r = [x for x in rows if x[0] == b][0]
    log(f"   b={b:4d} psi={r[1]:.6f} lA={r[2]:.3e} theta_w={r[3]:.5f} kappa_max={r[4]:.3e} (ii)k={r[5]:.3e} (iii)k={r[6]:.3e} Q1={r[7]:.4f} Q2'={r[8]:.3e}")
# rational witness for b=5: psi = 32/47 with tau0^47 * 5^32 <= 1
tau0 = recTau(5, 0)
log(f"   b=5 rational witness psi=32/47: tau0^47*5^32 <= 1: {tau0**47 * 5**32 <= 1}; 32/47={32/47:.6f} > 2theta=0.68: {F(32,47) > F(68,100)}")
open(sys.argv[1] if len(sys.argv) > 1 else '/dev/null', 'w').write("\n".join(out) + "\n")
