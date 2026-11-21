from fractions import Fraction as Fr
import math, itertools
lam=Fr(8,5); E=Fr(17813,10000)  # e^gamma <= e^0.5773 < 1.7813
def logub(r):  # upper bound of log r for r>1 via log(1+t) <= t - t^2/2 + t^3/3
    t=r-1; return t-t*t/2+t**3/3
def gK(v, cgrid):
    if v<=1: return v
    s=Fr(0)
    for c,c2 in zip(cgrid,cgrid[1:]):
        if c>=v: break
        s+=(v-c)*logub(min(c2,v)/c) if False else (v-c)*logub(c2/c)
    return v-s
def ladder_val(v, lad, cgrid, cache):
    # largest ladder point <= v
    best=None
    for l in lad:
        if l<=v: best=l
    if best is None: return None
    if best not in cache: cache[best]=gK(best,cgrid)
    return cache[best]
def tau(vb):
    fv=math.floor(vb)
    best=min(Fr(27183,10000)**(k-1)*Fr(1,k)**fv for k in range(2,30))
    return best
def run(Rgrid,Bgrid,lad,cgrid,slack=Fr(1,100)):
    cache={}
    eR=Fr(0)
    for a,b in zip(Rgrid,Rgrid[1:]):
        vb=Fr(12,5)-10*b
        if vb<=1: G=vb
        else: G=ladder_val(vb,lad,cgrid,cache)
        eR+=E*(1-a/Fr(23,100))/G*logub(b/a)
    eB=Fr(0)
    for a,b in zip(Bgrid,Bgrid[1:]):
        vb=Fr(3,25)/b-Fr(1,2)
        g=ladder_val(min(vb,Fr(27,10)),lad,cgrid,cache)
        F1=E/g
        t=tau(vb); F2=1/(1-t) if t<1 else None
        F=min(F1,F2) if F2 else F1
        eB+=Fr(1,20)/a*(F-1)*logub(b/a)
    W=lam*(1-eB)-eR
    return float(eR),float(eB),float(W)
def arith(a,b,n): return [a+(b-a)*Fr(i,n) for i in range(n+1)]
def geomr(a,b,r):
    g=[a]
    while g[-1]*r<b: g.append(g[-1]*r)
    g.append(b); return g
for nR,nB,nl,nc in [(36,20,20,34),(48,24,30,40),(72,40,35,68),(36,16,18,20),(30,16,18,20)]:
    Rg=geomr(Fr(1,20),Fr(23,100),Fr(1,1)+Fr(1,nR//2*1)) if False else None
    Rg=[Fr(1,20)*Fr(23,5)**Fr(0)]  # placeholder
    # use arithmetic grids in log-ish spacing: arithmetic in 1/u for Buchstab, arithmetic in u for Richert
    Rg=arith(Fr(1,20),Fr(23,100),nR)
    Bg=[Fr(3,25)/(Fr(1,2)+v) for v in reversed(arith(Fr(19,10),Fr(23,2),nB))]  # u from 1/100 to 1/20 via v grid
    lad=arith(Fr(1),Fr(27,10),nl)
    cg=arith(Fr(1),Fr(28,10),nc)
    print(nR,nB,nl,nc, run(Rg,Bg,lad,cg), "Bgrid ends", float(Bg[0]), float(Bg[-1]))
