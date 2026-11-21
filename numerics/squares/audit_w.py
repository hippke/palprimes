r"""Independent audit checks for Prop. W (odd length 2M+1, TP's Pi_b(2M)).
(a) even/odd-length Lemma 3 by exhaustive search (small b, L)
(b) exact A1 = sum_p p^2 Pr(Y = Y' mod p^2), A3, SV via residue histograms, versus
    collision bound  sum_p p^2 (||f||^2 + Pr(W in p^2 Z \ 0)) and the local-count LS bound
(c) direct sum over points of prod psi (Fourier side) equals the residue side."""
import itertools, numpy as np, sympy, sys
def lemma3(b, n):  # symmetric t of length n, |t_j|<=2b-2: count nonzero with sum t_j b^j = 0
    h = (n+1)//2; cnt = 0
    w = [b**j + (b**(n-1-j) if n-1-j != j else 0) for j in range(h)]
    for t in itertools.product(range(-(2*b-2), 2*b-1), repeat=h):
        if any(t) and sum(a*c for a, c in zip(t, w)) == 0: cnt += 1
    return cnt
for b in (2, 3, 4):
    for n in range(2, {2: 13, 3: 10, 4: 8}[b]):
        c = lemma3(b, n)
        if c: print("LEMMA3 FAIL", b, n, c)
print("lemma3 even+odd lengths: done", flush=True)
def law(cs, doubled):
    """exact law as dict value->prob"""
    f = {0: 1.0}
    for c, dbl in zip(cs, doubled):
        k = {}
        for d in range(b):
            for e in (range(b) if dbl else [0]):
                k[(d+e)*c] = k.get((d+e)*c, 0) + (1/b**2 if dbl else 1/b)
        g = {}
        for y, py in f.items():
            for z, pz in k.items():
                g[y+z] = g.get(y+z, 0) + py*pz
        f = g
    return f
def resid_coll(f, q):
    hist = np.zeros(q)
    for y, py in f.items(): hist[y % q] += py
    return (hist**2).sum()
b, M, P, v, k1, k2, k3 = [int(a) for a in sys.argv[1:8]]
cj = lambda j: b**j + b**(2*M-j) if j < M else b**M      # odd length 2M+1
inner = list(range(M-k1-k2, M))                             # K2 then K1 (innermost), middle digit dropped (psi<=1)
m = M-k1-k2
K1 = list(range(M-k1, M)); K2 = list(range(M-k1-k2, M-k1)); K3 = list(range(M-k1-k2-k3, M-k1-k2)); V = list(range(v))
assert v <= M-k1-k2-k3
ps = list(sympy.primerange(P, 2*P))
f1 = law([cj(j)//b**m for j in K2+K1], [False]*k2+[True]*k1)
f3 = law([cj(j) for j in K2+K3], [False]*k2+[True]*k3)
fV = law([cj(j) for j in V], [False]*v)
g = (2*b*b+1)/(3*b*b)
n1, n3, nV = [sum(v*v for v in f.values()) for f in (f1, f3, fV)]
print(f"b={b} M={M} P={P} V={v} K1={k1} K2={k2} K3={k3}  N1={max(f1)+1}")
print(f" ||f1||^2 {n1:.6g} vs Lemma3 {(g/b)**k1*b**-k2:.6g}; ||f3||^2 {n3:.6g} vs {(g/b)**k3*b**-k2:.6g}; ||fV||^2 {nV:.6g} vs {b**-v:.6g}")
A1 = sum(p*p*resid_coll(f1, p*p) for p in ps)
A3 = sum(p*p*resid_coll(f3, p*p) for p in ps)
SV = sum(p*p*resid_coll(fV, p*p) for p in ps)
# Fourier side check of A1 at one prime
p = ps[0]; q = p*p; h = np.arange(q)
four = 0
for hh in h:
    a = hh/q
    four += np.prod([ (abs(np.exp(2j*np.pi*np.arange(b)*((cj(j)*hh) % q)/q).sum())/b)**(4 if j in K1 else 2) for j in K1+K2])
print(f" Fourier vs residue at p={p}: {four:.6g} vs {q*resid_coll(f1, q):.6g}")
# collision bound: Pr(W = w) <= ||f||^2, W in p^2 Z\0 with |W| < N1
N1 = max(f1)+1
coll = sum(p*p*(n1 + 2*(N1//(p*p))*n1) for p in ps)
K = sum(2*p*p/N1 + 1 for p in ps) + 1
LS = 2*N1*2*K*n1
print(f" A1 = {A1:.6g} <= collision bound {coll:.6g} <= LS bound {LS:.6g}   P^3||f1||^2 = {P**3*n1:.4g}")
print(f" A3 = {A3:.6g}, diag sum p^2 ||f3||^2 = {sum(p*p for p in ps)*n3:.4g}; SV = {SV:.6g}, diag {sum(p*p for p in ps)*nV:.4g}, 4P^2 = {4*P*P}")
