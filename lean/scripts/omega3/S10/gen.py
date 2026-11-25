"""S10 generator: rational band data + exact integer mirror of the Lean checker (Omega3/Items/S10_*.lean)."""
import sys, json, math, numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, "/astro/palindromic-primes/lean/omega3/main/reports/S10_scratch")
import design as D
Q = 2**20; PB = 64; TP = 2**PB; E = 10**5; NS = 12; QN = Q*NS; D0 = 10**7   # eps0 = 1/D0
U = Fr(83, 85); M = Fr(1, 85); K2 = Fr(9999, 1000)

def ceil_div(a, b): return -((-a)//b)
def tsub(a, b): return a - b if a > b else 0
# ---------- log chain ----------
def logstep(n, n2):
    d = n - n2
    assert 0 < d < n2
    pa = 12*d*n2**3 + 4*d**3*n2; pb = 6*d*d*n2*n2 + 3*d**4
    den = 12*n2**4*(n2 - d)
    lowN = tsub(pa*(n2-d), pb*(n2-d) + 12*d**5)
    upN = tsub(pa*(n2-d) + 12*d**5, pb*(n2-d))
    return (TP*lowN)//den, ceil_div(TP*upN, den)
def logtab(sg, A0):
    tab = [(sg[0], 0, 0)]
    for n2 in sg[1:]:
        n, lo, hi = tab[-1]
        if n2 >= A0:
            a, b = logstep(n, n2); tab.append((n2, lo + a, hi + b))
        else:
            tab.append((n2, lo, hi))
    return tab
# ---------- phi bounds ----------
def phi_lohi(n, ln, hn, A, lA, hA, B, lB, hB):
    if n <= A: return 0, 0
    if n <= B:
        return tsub(n*tsub(lA, hn), (n-A)*TP), tsub(n*tsub(hA, ln), (n-A)*TP)
    return tsub(n*tsub(lA, hB), (B-A)*TP), tsub(n*tsub(hA, lB), (B-A)*TP)
def emin(cells, U1, U2):
    # cells: list of (A, m); mirror of eminRec with acc starting at 0
    acc = 0
    def rec(acc, l):
        if not l: return acc
        A, mm = l[0]
        if A <= U1: return rec(mm, l[1:])
        if U2 < A: return acc
        return min(acc, rec(mm, l[1:]))
    return rec(0, cells)
def band_check(sg, tab, edges, ms, xn_, xd_, verbose=False):
    """edges: A_0..A_J (cell left ends, Nat), last cell to Q; ms: Int eta numerators."""
    logd = {n: (lo, hi) for (n, lo, hi) in tab}
    J = len(edges)
    cells = []
    for j in range(J):
        A = edges[j]; B = edges[j+1] if j+1 < J else Q
        cells.append((A, logd[A][0], logd[A][1], B, logd[B][0], logd[B][1], ms[j]))
    P = []; N = []
    for (n, ln, hn) in tab:
        p = 0; q = 0
        for (A, lA, hA, B, lB, hB, mj) in cells:
            lo, hi = phi_lohi(n, ln, hn, A, lA, hA, B, lB, hB)
            if mj > 0: p += mj*lo
            elif mj < 0: q += (-mj)*hi
        P.append(p); N.append(q)
    # A(1) upper bound at n = Q (tab[0])
    n, ln, hn = tab[0]
    a1 = 0
    for (A, lA, hA, B, lB, hB, mj) in cells:
        lo, hi = phi_lohi(n, ln, hn, A, lA, hA, B, lB, hB)
        a1 += mj*hi if mj > 0 else mj*lo
    S = Q*TP*E; SQ = S*Q
    ec = [(c[0], c[6]) for c in cells]
    worst = None; fails = []
    for k in range(len(sg)-1):
        nh, nl = sg[k], sg[k+1]
        # relevant: u2 > 2m/(1-x)  <=> (Q-nl)*(xd-xn)*85 > 2*Q*xd
        if not ((Q-nl)*(xd_-xn_)*85 > 2*Q*xd_): continue
        em = emin(ec, Q-nh, Q-nl)
        c = em*Q*TP - a1
        cterm = c*(nl if c >= 0 else nh)
        G = (Q-nh)*TP*E*Q + cterm + (P[k+1] - N[k])*Q
        ok1 = G*D0 > SQ
        t2n = (Q-nl)*(xd_-xn_); t2d = 2*Q*xd_     # t2 = t2n/t2d
        ok = ok1
        if ok1 and t2n*85 > t2d:
            L = (D0-1)*(83*xd_-85*xn_)*(G*D0-SQ)**2            # / (D0*85*xd*(SQ*D0)^2)
            Ld = D0*85*xd_*(SQ*D0)**2
            okq = L*1000*t2d**2 >= 9999*t2n**2*Ld
            okl = L*85*t2d >= (85*t2n - t2d)*Ld
            ok = okq or okl
            # slack measure
            g = G/SQ; t2 = t2n/t2d; Wv = min(9.999*t2*t2, t2 - 1/85)
            rel = (float(U) - xn_/xd_)*(g-1e-7)**2/Wv - 1
            if worst is None or rel < worst[0]: worst = (rel, k, nh, nl)
        if not ok: fails.append(k)
    return fails, worst, a1
def Ktab(edges):
    J = len(edges); bs = [edges[j+1] if j+1 < J else Q for j in range(J)]
    pts_lo = []; pts_hi = []
    for j in range(J):
        A, B = edges[j], bs[j]
        pts_hi.append([A*NS + i*(B-A) for i in range(NS)])          # left ends (upper sums)
        pts_lo.append([A*NS + i*(B-A) for i in range(1, NS+1)])     # right ends (lower sums)
    def kfl(N1, N2): return (TP*min(N1*N2, (QN-N1)*(QN-N2)))//(N1*N2)
    def kcl(N1, N2): return ceil_div(TP*min(N1*N2, (QN-N1)*(QN-N2)), N1*N2)
    Klo = [[0]*J for _ in range(J)]; Khi = [[0]*J for _ in range(J)]
    for j in range(J):
        for l in range(J):
            w = (bs[j]-edges[j])*(bs[l]-edges[l])
            Klo[j][l] = w*sum(kfl(a, b) for a in pts_lo[j] for b in pts_lo[l])
            Khi[j][l] = w*sum(kcl(a, b) for a in pts_hi[j] for b in pts_hi[l])
    return Klo, Khi     # scale QN^2 * TP
def cost_check(tab, edges, ms, Klo, Khi):
    logd = {n: (lo, hi) for (n, lo, hi) in tab}
    J = len(edges); bs = [edges[j+1] if j+1 < J else Q for j in range(J)]
    pos = 0; neg = 0
    for j in range(J):
        A, B = edges[j], bs[j]
        Dhi = tsub(Q*tsub(logd[A][1], logd[B][0]), (B-A)*TP)       # scale Q*TP
        pos += ms[j]**2*Dhi*Q*NS*NS
    for j in range(J):
        for l in range(J):
            pr = ms[j]*ms[l]
            if pr > 0: neg += pr*Klo[j][l]
            elif pr < 0: pos += (-pr)*Khi[j][l]
    scale = E*E*Q*Q*NS*NS*TP
    return Fr(pos - neg, scale)    # >= c_eta - 1
if __name__ == "__main__":
    nb = int(sys.argv[1]); MC = int(sys.argv[2]); umin = float(sys.argv[3]); infl = float(sys.argv[4]); ratio = float(sys.argv[5])
    xs = [Fr(1, 3)] + [Fr(round((1/3 + (0.6251-1/3)*i/nb)*10000), 10000) for i in range(1, nb)] + [Fr(6251, 10000)]
    assert K2*(1-xs[-1])**2 <= 4*(U-xs[-1]) and xs[-1] <= 2*U-1
    ef = umin*(1/umin)**(np.arange(MC)/MC)
    edges = sorted(set(int(round(e*Q)) for e in ef))
    C = D.Cells(np.array([e/Q for e in edges] + [1.0]))
    Klo, Khi = Ktab(edges)
    # s-grid: geometric in u from ulo_min to 1-edges[0]/Q, plus cell edges, plus below A0
    ulo = 2/85/(1-float(xs[0]))*0.98
    us = list(np.geomspace(ulo, 1 - edges[0]/Q, int(math.log((1-edges[0]/Q)/ulo)/math.log(ratio)) + 1))
    sset = set(int(round((1-u)*Q)) for u in us) | set(edges) | {Q, 0}
    sset |= set(int(round(edges[0]*f)) for f in (0.75, 0.5, 0.25))
    out = {"Q": Q, "PB": PB, "E": E, "NS": NS, "D0": D0, "xs": [[x.numerator, x.denominator] for x in xs], "edges": edges, "bands": []}
    for it in range(8):
        sg = sorted(sset, reverse=True)
        tab = logtab(sg, edges[0])
        allok = True; out["bands"] = []; tot = Fr(0)
        for i in range(nb):
            x0 = float(xs[i])
            if it == 0 or True:
                pass
            if it == 0:
                eta, c1 = D.design_band(C, x0, infl)
                ms_i = [int(round(v*E)) for v in eta]
                out.setdefault("ms", []).append(ms_i)
            ms_i = out["ms"][i]
            fails, worst, a1 = band_check(sg, tab, edges, ms_i, xs[i].numerator, xs[i].denominator)
            cu = cost_check(tab, edges, ms_i, Klo, Khi)
            cn = math.ceil(cu*10**6) ; cn = max(cn, 0)
            I = U*Fr(xs[i+1]/xs[i]-1) + (1-U)*Fr((1-xs[i+1])/(1-xs[i])-1)
            tot += Fr(cn, 10**6)*I
            out["bands"].append({"cn": cn})
            print(f"it {it} band {i} fails {len(fails)} worst {worst[:2] if worst else None} c-1<= {float(cu):.6f} Icrude {float(I):.4f}", flush=True)
            if fails:
                allok = False
                for k in fails:
                    nh, nl = sg[k], sg[k+1]
                    if nh - nl > 1: sset.add((nh+nl)//2)
        print(f"it {it} grid {len(sg)} total cost bound {float(tot):.6f}", flush=True)
        if allok: break
    out["sg"] = sg
    json.dump(out, open(sys.argv[6], "w"))
