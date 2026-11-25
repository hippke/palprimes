"""S10 float design: Lemma A step functions per Sigma_2 band, condition reduced to the left band edge x_i (exact reduction)."""
import sys, numpy as np
from scipy.optimize import minimize
U = 83/85; m = 1/85; K2 = 9999/1000
def W(t):
    t = np.asarray(t, float)
    return np.where(t <= m, 0.0, np.minimum(K2*t*t, t - m))
def xn_min():
    lo, hi = 1/3, 2*U-1
    for _ in range(100):
        md = (lo+hi)/2
        if K2*(1-md)**2 <= 4*(U-md): hi = md
        else: lo = md
    return hi
def Hs(a, s):  # H(a,s) = s log(s/a) - s + a for s>=a
    s = np.asarray(s, float)
    return np.where(s >= a, s*np.log(np.maximum(s, a)/a) - s + a, 0.0)
class Cells:
    def __init__(s, edges):
        s.e = np.asarray(edges, float); s.lo = s.e[:-1]; s.hi = s.e[1:]; s.M = len(s.lo)
        s.D = np.log(s.hi/s.lo) - (s.hi - s.lo)
        s.Kl, s.Ku = s.Kb(12); s.Km = (s.Kl+s.Ku)/2
        s.Q = np.diag(s.D) - s.Km
    def amat(s, sv):
        sv = np.asarray(sv, float)
        return np.stack([Hs(s.lo[j], sv) - Hs(s.hi[j], sv) for j in range(s.M)], axis=-1)
    def Kb(s, ns):
        sub = np.concatenate([np.linspace(s.lo[j], s.hi[j], ns+1)[:-1] for j in range(s.M)] + [[s.e[-1]]])
        sl, sh = sub[:-1], sub[1:]; w = sh - sl
        rl, rh = (1-sl)/sl, (1-sh)/sh
        kup = np.minimum(1, np.outer(rl, rl))*np.outer(w, w); klo = np.minimum(1, np.outer(rh, rh))*np.outer(w, w)
        cell = np.repeat(np.arange(s.M), ns)
        Ku = np.zeros((s.M, s.M)); Kl = np.zeros((s.M, s.M))
        np.add.at(Ku, (cell[:, None], cell[None, :]), kup); np.add.at(Kl, (cell[:, None], cell[None, :]), klo)
        return Kl, Ku
    def gmat(s, u):
        u = np.asarray(u, float)
        A1 = s.amat(np.array([1.0]))[0]
        G = -np.outer(1-u, A1) + s.amat(1-u)
        j = np.searchsorted(s.e, u, side="right") - 1
        ok = (j >= 0)
        jj = np.clip(j, 0, s.M-1)
        G[np.arange(len(u))[ok], jj[ok]] += (1-u)[ok]
        return G   # g = u + G eta
def design_band(C, x0, infl, ng=1500):
    a = 2*m/(1-x0)
    uu = np.unique(np.concatenate([np.geomspace(a, 0.999, ng), C.e[1:-1]*(1-1e-9), C.e[1:-1]*(1+1e-9)]))
    uu = uu[(uu >= a) & (uu < 1)]
    T = np.sqrt(W(uu*(1-x0)/2)/(U-x0))
    G = C.gmat(uu)
    tgt = T*(1+infl) + 1e-6
    cons = [{"type": "ineq", "fun": lambda x: G@x + uu - tgt, "jac": lambda x: G}]
    r = minimize(lambda x: x@C.Q@x, np.zeros(C.M), jac=lambda x: 2*C.Q@x, constraints=cons, method="SLSQP",
                 options=dict(maxiter=1000, ftol=1e-15))
    return r.x, r.x@C.Q@r.x
def check_band(C, x0, eta, n=200000):
    a = 2*m/(1-x0)
    uu = np.geomspace(a, 1-1e-9, n)
    g = uu + C.gmat(uu)@eta
    T = np.sqrt(W(uu*(1-x0)/2)/(U-x0))
    return float(np.min(g - T)), float(np.min((g-T)/np.maximum(T,1e-9)))
def bandI(x0, x1): return U*np.log(x1/x0) + (1-U)*np.log((1-x1)/(1-x0))
if __name__ == "__main__":
    nb = int(sys.argv[1]); MC = int(sys.argv[2]); umin = float(sys.argv[3]); infl = float(sys.argv[4])
    xn = xn_min()*(1+1e-6)
    edges = umin*(1/umin)**(np.arange(MC+1)/MC); edges[-1] = 1.0
    C = Cells(edges)
    xs = np.linspace(1/3, xn, nb+1)
    tot = 0
    for i in range(nb):
        eta, c1 = design_band(C, xs[i], infl)
        sl = check_band(C, xs[i], eta)
        I = bandI(xs[i], xs[i+1]); tot += c1*I
        print(f"band {i} x0 {xs[i]:.4f} c-1 {c1:.5f} I {I:.4f} cost {c1*I:.6f} slack {sl[0]:.2e} rel {sl[1]:.2e} max|eta| {np.abs(eta).max():.3f} TV {np.abs(np.diff(np.r_[0,eta])).sum():.3f}")
    print("xn", xn, "total cost", tot)
