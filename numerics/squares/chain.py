"""Numerical check of the prime-square chain (Prop. W) on small cases.
Palindromes with 2M digits in base b: n = sum_{j<M} d_j c_j, c_j = b^j + b^{2M-1-j}.
Points: h/p^2 + beta, p prime in [P, 2P), h mod p^2.
Blocks (positions j): V = [0, v) outer; inner U = K3 | K2 | K1 with K1 innermost (j close to M).
Checks: (1) sum |fhat_all| <= (sum Pi_V psi)^1/2 (sum Pi_U psi)^1/2
        (2) sum Pi_U psi <= (A1')^1/2 (A3')^1/2
        (3) A1' <= (N1 + 1/delta) * M_delta * ||f1||^2 with delta = 1/N1 (Gallagher-type, constant check only)
        (4) A_l = sum_p p^2 Pr(Z = Z' mod p^2) >= sum Pi_l psi (identity with equality at beta=0)"""
import numpy as np, sys, sympy
b, M, P, v, k1, k2, k3 = [int(a) for a in sys.argv[1:8]]
beta = float(sys.argv[8]) if len(sys.argv) > 8 else 0.0
c = np.array([b**j + b**(2*M-1-j) for j in range(M)], dtype=object)
ps = list(sympy.primerange(P, 2*P))
pts = []; pw = []
for p in ps:
    q = p*p
    for h in range(q):
        pts.append((h % q) / q + beta)
pts = np.array(pts)
def psi_of(j):
    # psi(c_j alpha) computed with exact reduction of c_j mod q (alpha = h/q + beta)
    out = np.empty(len(pts)); i = 0
    for p in ps:
        q = p*p; cm = int(c[j] % q); h = np.arange(q)
        a = (cm*h % q)/q + (float(c[j] % (10**12)) * beta % 1.0 if beta else 0.0)
        t = np.exp(2j*np.pi*np.outer(np.arange(b), a)).sum(0)
        out[i:i+q] = (np.abs(t)/b)**2; i += q
    return out
V = list(range(0, v)); K1 = list(range(M-k1, M)); K2 = list(range(M-k1-k2, M-k1)); K3 = list(range(M-k1-k2-k3, M-k1-k2))
assert v <= M-k1-k2-k3, "blocks overlap"
PS = {j: psi_of(j) for j in range(M)}
prod = lambda J, e=1.0: np.prod([PS[j]**e for j in J], axis=0) if J else np.ones(len(pts))
L1 = prod(range(M), 0.5).sum()
SV = prod(V).sum(); U = K1+K2+K3; SU = prod(U).sum()
A1 = (prod(K1, 2)*prod(K2)).sum(); A3 = (prod(K3, 2)*prod(K2)).sum()
g = (2*b*b+1)/(3*b*b)
f1 = (g/b)**k1 * b**(-k2); f3 = (g/b)**k3 * b**(-k2)
N1 = 2*b**(2*(k1+k2)+1)
Mdelta = sum(2*p*p/N1 + 1 for p in ps)
LS = 2*N1*Mdelta*f1   # (N1 + N1) * M_delta * ||f1||^2
npts = len(pts)
print(f"b={b} M={M} P={P} #p={len(ps)} pts={npts} V={v} K1={k1} K2={k2} K3={k3} beta={beta}")
print(f" L1 sum|f|          = {L1:.4g}   trivial pts={npts}  P^2={P*P}")
print(f" (1) {L1:.4g} <= {np.sqrt(SV*SU):.4g}  {L1 <= np.sqrt(SV*SU)*(1+1e-9)}")
print(f" (2) {SU:.4g} <= {np.sqrt(A1*A3):.4g}  {SU <= np.sqrt(A1*A3)*(1+1e-9)}")
print(f" (3) A1'={A1:.4g} <= LS bound {LS:.4g}  {A1 <= LS}")
divb = np.log(2*b**(2*M))/(2*np.log(P))
A3b = sum(p*p for p in ps)*f3 + sum(p*p for p in ps)/len(ps)*0 + 4*P*P*divb*len(ps)/len(ps)
print(f" (4) A3'={A3:.4g} <= diag+div {sum(p*p for p in ps)*f3 + (2*P)**2*divb:.4g}  SV={SV:.4g} <= {sum(p*p for p in ps)*b**(-v) + (2*P)**2*divb:.4g}")
