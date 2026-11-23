"""Rigorous certification of a block majorant for the digits {0,1} in base r.

Input: a JSON file with r, l, p = p_num/p_den and integer coefficients ints[0..H], H = r^l - 1,
tau_u = ints[u] / 2^scale_log2 (exact dyadic rationals). The script proves, in interval arithmetic (arb),

    T(t) = tau_0 + 2 sum_{u=1}^{H} tau_u cos(2 pi u t)  >=  K(t)^p,   K(t) = prod_{0<=i<l} |cos(pi r^i t)|,

for all real t. Both sides are even and 1-periodic, so it suffices to cover [0, 1/2].

Method on a dyadic interval I = [m - h, m + h] (exact rational end points):
 T_lo = T(m) - |T'(m)| h + min(0, T''(m) - C3 h) h^2 / 2 with C3 = 2 sum tau_u (2 pi u)^3 >= sup |T'''|
 (Taylor with exact remainder).
 (A) crude test. sup_I K^p <= prod_i cos(pi dist(r^i I, Z))^p. Accept I if T_lo exceeds this.
 (B) if no factor vanishes on I, put D = T - K^p and accept if
     D(m) - |D'(m)| h + min(0, inf_I D'') h^2 / 2 > 0, with inf_I D'' from an arb ball evaluation.
 Otherwise bisect. All point values are arb balls at 192 bits.

Output: number of accepted intervals, smallest certified lower bound of T - K^p, tau_0, T(0) = A,
a rigorous lower bound for the level psi_T = -log_r(tau_0)/l, and log_r(A)/l.

Usage: python -I certify.py data/majorant_r3_l4.json [shift]
shift (integer) is added to ints[0] (a negative shift is a negative control and must FAIL).
Relative paths are resolved against the folder that contains scripts/.
"""
import sys, json, time, math
from pathlib import Path
from fractions import Fraction as Fr
from flint import arb, acb, acb_poly, ctx

ctx.prec = 192
ROOT = Path(__file__).resolve().parent.parent


def load(path):
    p = Path(path)
    if not p.is_absolute():
        p = ROOT / p
    return p, json.load(open(p))


def main():
    path, d = load(sys.argv[1])
    shift = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    assert d.get("kind", "dm") == "dm"
    r, l = d["r"], d["l"]
    p = arb(d["p_num"]) / d["p_den"]
    pF = Fr(d["p_num"], d["p_den"])
    S = 2 ** d["scale_log2"]
    ints = list(d["ints"])
    ints[0] += shift
    H = len(ints) - 1
    assert H == r ** l - 1 and min(ints[1:]) >= 0 and ints[0] > 0
    tau = [arb(x) / S for x in ints]
    PI = arb.pi()
    twopi = 2 * PI
    P0 = acb_poly([acb(0)] + [acb(tau[u]) for u in range(1, H + 1)])
    P1 = acb_poly([acb(0)] + [acb(tau[u] * u) for u in range(1, H + 1)])
    P2 = acb_poly([acb(0)] + [acb(tau[u] * u * u) for u in range(1, H + 1)])
    C3 = 2 * sum(tau[u] * (twopi * u) ** 3 for u in range(1, H + 1))
    A_exact = Fr(ints[0] + 2 * sum(ints[1:]), S)
    tau0_exact = Fr(ints[0], S)

    def A(x):
        return arb(x.numerator) / x.denominator

    def Tder(m):
        z = acb(arb.cos_pi(2 * m), arb.sin_pi(2 * m))
        v0, v1, v2 = P0(z), P1(z), P2(z)
        T = tau[0] + 2 * v0.real
        T1 = -2 * twopi * v1.imag
        T2 = -2 * twopi ** 2 * v2.real
        return T, T1, T2

    def dist_to_Z(lo, hi):
        """min of ||y|| over y in [lo, hi] (exact rationals)."""
        if math.floor(hi) > math.floor(lo) or lo == math.floor(lo):
            return Fr(0)
        n = math.floor(lo)
        return min(lo - n, n + 1 - hi)

    def has_half(lo, hi):
        """True if [lo, hi] contains a half-integer (a zero of cos(pi y))."""
        a = lo - Fr(1, 2)
        return math.floor(hi - Fr(1, 2)) > math.floor(a) or a == math.floor(a)

    def logK_derivs(t):
        """K^p = exp(L), returns K^p, L', L'' at an arb point or ball t (no zero of K on t)."""
        L = arb(0); L1 = arb(0); L2 = arb(0)
        for i in range(l):
            y = r ** i * t
            c = arb.cos_pi(y); s = arb.sin_pi(y)
            L += (c * c).log() / 2
            L1 += -PI * r ** i * s / c
            L2 += -(PI * r ** i) ** 2 / (c * c)
        return (p * L).exp(), p * L1, p * L2

    def check(lo, hi):
        m = (lo + hi) / 2; h = (hi - lo) / 2
        mA = A(m); hA = A(h)
        T, T1, T2 = Tder(mA)
        T2lo = T2 - C3 * hA
        Tlo = T - abs(T1) * hA + (T2lo.lower() if T2lo.lower() < 0 else arb(0)) * hA * hA / 2
        Kup = arb(1)
        for i in range(l):
            Kup *= arb.cos_pi(A(dist_to_Z(r ** i * lo, r ** i * hi)))
        u = Kup.upper()
        Gup = (arb(u).log() * p).exp() if u > 0 else arb(0)
        lbA = Tlo - Gup
        if lbA > 0:
            return True, float(lbA.lower())
        if any(has_half(r ** i * lo, r ** i * hi) for i in range(l)):
            return False, float(lbA.lower())
        G, L1, L2 = logK_derivs(mA)
        D0 = T - G
        D1 = T1 - G * L1
        Gb, L1b, L2b = logK_derivs(arb(mA, hA))
        D2 = arb(T2, C3 * hA) - Gb * (L1b * L1b + L2b)
        if not D2.is_finite():
            return False, float(lbA.lower())
        D2lo = D2.lower()
        lbB = D0 - abs(D1) * hA + (D2lo if D2lo < 0 else arb(0)) * hA * hA / 2
        return (lbB > 0), float(lbB.lower())

    t0 = time.time()
    stack = [(Fr(k, 2 ** 10), Fr(k + 1, 2 ** 10), 10) for k in range(2 ** 9)]
    nint = 0; minlb = 1.0; maxdep = 0; fails = []
    while stack:
        lo, hi, dep = stack.pop()
        ok, lb = check(lo, hi)
        if ok:
            nint += 1; minlb = min(minlb, lb); maxdep = max(maxdep, dep)
        elif dep >= 60:
            fails.append((float(lo), float(hi), lb))
            if len(fails) > 20:
                break
        else:
            mid = (lo + hi) / 2
            stack.append((lo, mid, dep + 1)); stack.append((mid, hi, dep + 1))
    ok = not fails and not stack
    # rigorous lower bound of psi_T = -log(tau_0)/(l log r) and upper bound of log_r(A)/l
    psi = -(A(tau0_exact).log()) / (arb(r).log() * l)
    lA = A(A_exact).log() / (arb(r).log() * l)
    print(f"file={path.relative_to(ROOT) if path.is_relative_to(ROOT) else path} r={r} l={l} p={pF} H={H} shift={shift}")
    print(f"intervals={nint} maxdepth={maxdep} fails={len(fails)} "
          f"min_certified_lower_bound={minlb:.3e} time={time.time() - t0:.1f}s")
    for f in fails[:5]:
        print("  FAIL", f)
    print(f"tau0={float(tau0_exact):.12f} T(0)=A={float(A_exact):.12f}")
    print(f"psi_T = -log_r(tau0)/l in {psi.str(12, radius=False)} (lower bound {float(psi.lower()):.10f}), "
          f"log_r(A)/l <= {float(lA.upper()):.3e}")
    print(f"CERTIFIED={ok}")


if __name__ == "__main__":
    main()
