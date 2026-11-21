"""Variant of sieve_feasibility.py: prime cubes p^3 | n with p >= x^alpha are excluded outright
(middle-block injectivity: A_{p^3} <= b X / p^{3/2}, summable with a power saving), so only
exponents a_i in {1, 2} remain; squares of primes p < x^c0 are assumed controlled."""
import sys, itertools, numpy as np
argv = sys.argv[:]; sys.argv = [sys.argv[0]]
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sieve_feasibility as sf
from scipy.optimize import linprog
MAXE = 2
def omega_ok(lam, al, be, c0, maxe=MAXE):
    parts = [p for om in range(1, 7) for p in itertools.combinations_with_replacement(range(1, maxe+1), om) if sum(p) == 6]
    for a in parts:
        om = len(a)
        if sum(a[i]*al for i in range(om)) > 1: continue
        c = np.r_[np.zeros(om), np.ones(om)]
        A = []; bnd = []
        for i in range(om):
            row = np.zeros(2*om); row[i] = -1/be; row[om+i] = -1; A.append(row); bnd.append(-1)
        A.append(np.r_[np.array(a, float), np.zeros(om)]); bnd.append(1)
        bounds = [((max(c0, al) if a[i] >= 2 else al), 1) for i in range(om)] + [(0, None)]*om
        r = linprog(c, A_ub=np.array(A), b_ub=bnd, bounds=bounds)
        if r.status == 0 and r.fun < lam - 1e-12: return False, a
    return True, None
sf.omega_ok = omega_ok
if __name__ == "__main__":
    grid = int(argv[1]); MAXE = int(argv[4]) if len(argv) > 4 else 2
    for th in [float(t) for t in argv[2].split(',')]:
        for c0 in [float(c) for c in argv[3].split(',')]:
            for name, FF, ff in [("JR", sf.FJR, sf.fJR), ("crude", sf.Fc, sf.fc1)]:
                v = sf.best(th, c0, FF, ff, grid=grid)
                print(f"maxe={MAXE} theta={th} c0={c0} {name}: W/XV={v[0]:+.4f} params={v[1:]}", flush=True)
