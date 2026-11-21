"""Feasibility of Omega<=5 at level theta with Richert weights (distinct primes),
squares of primes p > x^c0 handled through the weight constraints instead of a
square-moduli equidistribution input. Optimal (Jurkat-Richert) and crude sieve functions."""
import numpy as np, itertools, sys
from scipy.optimize import linprog
from scipy.integrate import quad
EG = np.exp(np.euler_gamma)
# ---- Jurkat-Richert F,f on a grid via (sF)'=f(s-1), (sf)'=F(s-1)
h = 1e-4; S = np.arange(0, 40+h, h)
F = np.where(S > 0, 2*EG/np.maximum(S, 1e-12), 0.0); f = np.zeros_like(S)
i2 = int(round(2/h)); i3 = int(round(3/h)); i1 = int(round(1/h))
for i in range(i2, len(S)):           # f from s=2, F from s=3
    s = S[i]
    if i > i2:
        f[i] = (S[i-1]*f[i-1] + h*0.5*(F[i-1-i1]+F[i-i1]))/s
    if i > i3:
        F[i] = (S[i-1]*F[i-1] + h*0.5*(f[i-1-i1]+f[i-i1]))/s
FJR = lambda s: np.interp(s, S, F) if s > 0 else np.inf
fJR = lambda s: np.interp(s, S, f)
# ---- crude: Selberg Lambda^2 upper bound F_c(s)=e^g/I(s/2), I(u)=int_0^u rho ; f_c by one Buchstab step
uu = np.arange(0, 60, 1e-3); rho = np.ones_like(uu)
for i, u in enumerate(uu):
    if u > 1:
        j = int(round((u-1)/1e-3)); rho[i] = rho[i-1] - 1e-3*rho[j]/u
I = np.concatenate([[0], np.cumsum((rho[1:]+rho[:-1])/2)*1e-3])
Fc = lambda s: EG/np.interp(s/2, uu, I) if s > 0 else np.inf
vv = np.arange(0.5, 60, 1e-3); tail = np.array([Fc(v)-1 for v in vv])
cumtail = np.concatenate([[0], np.cumsum((tail[1:]+tail[:-1])/2)*1e-3]); tot = cumtail[-1]
fc1 = lambda s: 1 - (tot - np.interp(s-1, vv, cumtail))/s
def W(lam, al, be, th, FF, ff):
    s = th/al
    val, _ = quad(lambda u: (1-u/be)*FF((th-u)/al)/u, al, be, limit=200)
    return lam*ff(s) - val
# ---- Omega constraint: every n<=x, P^-(n)>=x^al, w(n)>0, squares only of primes >= x^c0 -> Omega<=5
def omega_ok(lam, al, be, c0):
    # a bad n with Omega>=6 reduces to one with Omega = 6 (drop prime factors), so partitions of 6 suffice
    parts = [p for om in range(1, 7) for p in itertools.combinations_with_replacement(range(1, 7), om) if sum(p) == 6]
    for a in parts:
            om = len(a)
            if sum(a[i]*al for i in range(om)) > 1: continue
            # vars t_1..t_om, e_1..e_om ; min sum e  s.t. e_i >= 1 - t_i/be, e>=0, sum a t <= 1, t_i>=al (>=c0 if a_i>=2)
            c = np.r_[np.zeros(om), np.ones(om)]
            A = []; bnd = []
            for i in range(om):
                row = np.zeros(2*om); row[i] = -1/be; row[om+i] = -1; A.append(row); bnd.append(-1)
            row = np.r_[np.array(a, float), np.zeros(om)]; A.append(row); bnd.append(1)
            bounds = [((c0 if a[i] >= 2 else al), 1) for i in range(om)] + [(0, None)]*om
            r = linprog(c, A_ub=np.array(A), b_ub=bnd, bounds=bounds)
            if r.status == 0 and r.fun < lam - 1e-12: return False, a
            # status 2 = infeasible: fine
    return True, None
def best(th, c0, FF, ff, grid=40):
    bestv = (-np.inf,)
    for al in np.linspace(th/4.0, th/2.0, grid):
        for be in np.linspace(max(al*1.01, 1/6+1e-3), th - 1e-4, grid):
            # largest lam allowed by Omega constraint (bisection)
            lo, hi = 0.0, 6.0
            if not omega_ok(lo + 1e-9, al, be, c0)[0]: continue
            for _ in range(25):
                mid = (lo+hi)/2
                (lo, hi) = (mid, hi) if omega_ok(mid, al, be, c0)[0] else (lo, mid)
            v = W(lo, al, be, th, FF, ff)
            if v > bestv[0]: bestv = (v, al, be, lo)
    return bestv
if __name__ == "__main__":
    print("check JR: f(4)=%.4f (2e^g ln3/4=%.4f), F(3)=%.4f; crude Fc(2)=%.4f Fc(3)=%.4f Fc(6)=%.4f fc1(4)=%.4f fc1(3)=%.4f"
          % (fJR(4), 2*EG*np.log(3)/4, FJR(3), Fc(2), Fc(3), Fc(6), fc1(4), fc1(3)))
    for th in [float(t) for t in sys.argv[2].split(',')]:
        for c0 in [float(c) for c in sys.argv[3].split(',')]:
            for name, FF, ff in [("JR", FJR, fJR), ("crude", Fc, fc1)]:
                v = best(th, c0, FF, ff, grid=int(sys.argv[1]) if len(sys.argv) > 1 else 14)
                print(f"theta={th} c0={c0} {name}: W/XV={v[0]:+.4f} params={v[1:]}", flush=True)
